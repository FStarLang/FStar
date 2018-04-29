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
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3713 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3713 with
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
  fun uu____3794  ->
    match uu____3794 with
    | (t_base,refopt) ->
        let uu____3827 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3827 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3867 =
      let uu____3870 =
        let uu____3873 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3896  ->
                  match uu____3896 with | (uu____3903,uu____3904,x) -> x))
           in
        FStar_List.append wl.attempting uu____3873  in
      FStar_List.map (wl_prob_to_string wl) uu____3870  in
    FStar_All.pipe_right uu____3867 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3923 =
          let uu____3936 =
            let uu____3937 = FStar_Syntax_Subst.compress k  in
            uu____3937.FStar_Syntax_Syntax.n  in
          match uu____3936 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3990 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3990)
              else
                (let uu____4004 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4004 with
                 | (ys',t1,uu____4027) ->
                     let uu____4032 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4032))
          | uu____4073 ->
              let uu____4074 =
                let uu____4085 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4085)  in
              ((ys, t), uu____4074)
           in
        match uu____3923 with
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
                 let uu____4134 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4134 c  in
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
             let uu____4187 = p_guard_uvar prob  in
             match uu____4187 with
             | (xs,uv) ->
                 ((let uu____4195 =
                     FStar_Syntax_Unionfind.find
                       uv.FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____4195 with
                   | FStar_Pervasives_Native.None  ->
                       ((let uu____4199 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____4199
                         then
                           let uu____4200 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____4201 = print_ctx_uvar uv  in
                           let uu____4202 =
                             FStar_Syntax_Print.term_to_string phi  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____4200
                             uu____4201 uu____4202
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
                   | FStar_Pervasives_Native.Some uu____4208 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___133_4211 = wl  in
                   {
                     attempting = (uu___133_4211.attempting);
                     wl_deferred = (uu___133_4211.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___133_4211.defer_ok);
                     smt_ok = (uu___133_4211.smt_ok);
                     tcenv = (uu___133_4211.tcenv);
                     wl_implicits = (uu___133_4211.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4232 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____4232
         then
           let uu____4233 = FStar_Util.string_of_int pid  in
           let uu____4234 =
             let uu____4235 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4235 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4233 uu____4234
         else ());
        commit sol;
        (let uu___134_4242 = wl  in
         {
           attempting = (uu___134_4242.attempting);
           wl_deferred = (uu___134_4242.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___134_4242.defer_ok);
           smt_ok = (uu___134_4242.smt_ok);
           tcenv = (uu___134_4242.tcenv);
           wl_implicits = (uu___134_4242.wl_implicits)
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
             | (uu____4304,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4330 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4330
              in
           (let uu____4336 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____4336
            then
              let uu____4337 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4338 =
                let uu____4339 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4339 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4337 uu____4338
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
        let uu____4364 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4364 FStar_Util.set_elements  in
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
      let uu____4398 = occurs uk t  in
      match uu____4398 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4427 =
                 let uu____4428 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4429 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4428 uu____4429
                  in
               FStar_Pervasives_Native.Some uu____4427)
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
            let uu____4518 = maximal_prefix bs_tail bs'_tail  in
            (match uu____4518 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____4562 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____4610  ->
             match uu____4610 with
             | (x,uu____4620) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____4633 = FStar_List.last bs  in
      match uu____4633 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____4651) ->
          let uu____4656 =
            FStar_Util.prefix_until
              (fun uu___106_4671  ->
                 match uu___106_4671 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____4673 -> false) g
             in
          (match uu____4656 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____4686,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____4722 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____4722 with
        | (pfx,uu____4732) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____4744 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____4744 with
             | (uu____4751,src',wl1) ->
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
      let uu____4831 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____4885  ->
                fun uu____4886  ->
                  match (uu____4885, uu____4886) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4967 =
                        let uu____4968 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____4968  in
                      if uu____4967
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____4993 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____4993
                         then
                           let uu____5006 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____5006)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____4831 with | (isect,uu____5043) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5072 'Auu____5073 .
    (FStar_Syntax_Syntax.bv,'Auu____5072) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5073) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5130  ->
              fun uu____5131  ->
                match (uu____5130, uu____5131) with
                | ((a,uu____5149),(b,uu____5151)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5166 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5166) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5196  ->
           match uu____5196 with
           | (y,uu____5202) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5213 'Auu____5214 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5213) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5214)
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
                   let uu____5323 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5323
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____5331 =
                        let uu____5334 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____5334 :: seen  in
                      aux uu____5331 args2)
               | uu____5335 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____5348 .
    ('Auu____5348,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____5359  ->
    match uu____5359 with
    | (uu____5366,c,args) ->
        let uu____5369 = print_ctx_uvar c  in
        let uu____5370 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____5369 uu____5370
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5376 =
      let uu____5377 = FStar_Syntax_Subst.compress t  in
      uu____5377.FStar_Syntax_Syntax.n  in
    match uu____5376 with
    | FStar_Syntax_Syntax.Tm_uvar uu____5380 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____5381;
           FStar_Syntax_Syntax.pos = uu____5382;
           FStar_Syntax_Syntax.vars = uu____5383;_},uu____5384)
        -> true
    | uu____5405 -> false
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> flex_t) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar uv -> (t, uv, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uv;
           FStar_Syntax_Syntax.pos = uu____5423;
           FStar_Syntax_Syntax.vars = uu____5424;_},args)
        -> (t, uv, args)
    | uu____5446 -> failwith "Not a flex-uvar"
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5474 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5511 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5517 -> false
  
let string_of_option :
  'Auu____5524 .
    ('Auu____5524 -> Prims.string) ->
      'Auu____5524 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___107_5539  ->
      match uu___107_5539 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5545 = f x  in Prims.strcat "Some " uu____5545
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___108_5550  ->
    match uu___108_5550 with
    | MisMatch (d1,d2) ->
        let uu____5561 =
          let uu____5562 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5563 =
            let uu____5564 =
              let uu____5565 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5565 ")"  in
            Prims.strcat ") (" uu____5564  in
          Prims.strcat uu____5562 uu____5563  in
        Prims.strcat "MisMatch (" uu____5561
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___109_5570  ->
    match uu___109_5570 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5585 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5615 = m2 ()  in
          (match uu____5615 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5630 -> HeadMatch)
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5643 ->
          let uu____5644 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5644 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5655 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5678 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5687 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5715 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5715
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5716 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5717 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5718 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5719 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5732 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5756) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5762,uu____5763) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5805) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5826;
             FStar_Syntax_Syntax.index = uu____5827;
             FStar_Syntax_Syntax.sort = t2;_},uu____5829)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5836 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5837 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5838 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5851 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5858 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5876 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5876
  
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
            let uu____5903 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5903
            then FullMatch
            else
              (let uu____5905 =
                 let uu____5914 =
                   let uu____5917 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5917  in
                 let uu____5918 =
                   let uu____5921 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5921  in
                 (uu____5914, uu____5918)  in
               MisMatch uu____5905)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5927),FStar_Syntax_Syntax.Tm_uinst (g,uu____5929)) ->
            let uu____5938 = head_matches env f g  in
            FStar_All.pipe_right uu____5938 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5941 = FStar_Const.eq_const c d  in
            if uu____5941
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar uv,FStar_Syntax_Syntax.Tm_uvar uv') ->
            let uu____5949 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____5949
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5956),FStar_Syntax_Syntax.Tm_refine (y,uu____5958)) ->
            let uu____5967 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5967 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5969),uu____5970) ->
            let uu____5975 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5975 head_match
        | (uu____5976,FStar_Syntax_Syntax.Tm_refine (x,uu____5978)) ->
            let uu____5983 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5983 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5984,FStar_Syntax_Syntax.Tm_type
           uu____5985) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5986,FStar_Syntax_Syntax.Tm_arrow uu____5987) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6013),FStar_Syntax_Syntax.Tm_app (head',uu____6015))
            ->
            let uu____6056 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6056 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6058),uu____6059) ->
            let uu____6080 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6080 head_match
        | (uu____6081,FStar_Syntax_Syntax.Tm_app (head1,uu____6083)) ->
            let uu____6104 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6104 head_match
        | uu____6105 ->
            let uu____6110 =
              let uu____6119 = delta_depth_of_term env t11  in
              let uu____6122 = delta_depth_of_term env t21  in
              (uu____6119, uu____6122)  in
            MisMatch uu____6110
  
let head_matches_delta :
  'Auu____6139 .
    FStar_TypeChecker_Env.env ->
      'Auu____6139 ->
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
            let uu____6178 = FStar_Syntax_Util.head_and_args t  in
            match uu____6178 with
            | (head1,uu____6194) ->
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
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___135_6633 = p  in
      let uu____6636 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____6637 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___135_6633.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____6636;
        FStar_TypeChecker_Common.relation =
          (uu___135_6633.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____6637;
        FStar_TypeChecker_Common.element =
          (uu___135_6633.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___135_6633.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___135_6633.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___135_6633.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___135_6633.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___135_6633.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____6651 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____6651
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____6656 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____6678 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____6678 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____6686 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____6686 with
           | (lh,lhs_args) ->
               let uu____6721 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____6721 with
                | (rh,rhs_args) ->
                    let uu____6756 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6769,FStar_Syntax_Syntax.Tm_uvar uu____6770)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____6823 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6846,uu____6847)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____6850,FStar_Syntax_Syntax.Tm_uvar uu____6851)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6854,FStar_Syntax_Syntax.Tm_type uu____6855)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___136_6859 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___136_6859.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___136_6859.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___136_6859.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___136_6859.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___136_6859.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___136_6859.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___136_6859.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___136_6859.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___136_6859.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____6862,FStar_Syntax_Syntax.Tm_uvar uu____6863)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___136_6867 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___136_6867.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___136_6867.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___136_6867.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___136_6867.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___136_6867.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___136_6867.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___136_6867.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___136_6867.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___136_6867.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____6870,FStar_Syntax_Syntax.Tm_uvar uu____6871)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6874,uu____6875)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____6878,FStar_Syntax_Syntax.Tm_uvar uu____6879)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____6882,uu____6883) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____6756 with
                     | (rank,tp1) ->
                         let uu____6896 =
                           FStar_All.pipe_right
                             (let uu___137_6900 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___137_6900.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___137_6900.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___137_6900.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___137_6900.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___137_6900.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___137_6900.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___137_6900.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___137_6900.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___137_6900.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____6896))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____6906 =
            FStar_All.pipe_right
              (let uu___138_6910 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___138_6910.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___138_6910.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___138_6910.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___138_6910.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___138_6910.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___138_6910.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___138_6910.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___138_6910.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___138_6910.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____6906)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____6971 probs =
      match uu____6971 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____7052 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____7073 = rank wl.tcenv hd1  in
               (match uu____7073 with
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
                      (let uu____7132 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7136 = FStar_Option.get min_rank  in
                            rank_leq rank1 uu____7136)
                          in
                       if uu____7132
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
          let uu____7208 = destruct_flex_t t  in
          match uu____7208 with
          | (uu____7209,u,uu____7211) ->
              FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
                (FStar_Util.for_some
                   (fun uu____7225  ->
                      match uu____7225 with
                      | (y,uu____7231) ->
                          FStar_All.pipe_right bs
                            (FStar_Util.for_some
                               (fun uu____7245  ->
                                  match uu____7245 with
                                  | (x,uu____7251) ->
                                      FStar_Syntax_Syntax.bv_eq x y))))
           in
        let uu____7252 = rank tcenv p  in
        match uu____7252 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____7259 -> true
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
                      (flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                        ||
                        (flex_will_be_closed p2.FStar_TypeChecker_Common.rhs)))
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string [@@deriving show]
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____7286 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____7300 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____7314 -> false
  
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
                        let uu____7366 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____7366 with
                        | (k,uu____7372) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____7382 -> false)))
            | uu____7383 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____7435 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____7441 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____7441 = (Prims.parse_int "0")))
                           in
                        if uu____7435 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____7457 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____7463 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____7463 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____7457)
               in
            let uu____7464 = filter1 u12  in
            let uu____7467 = filter1 u22  in (uu____7464, uu____7467)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____7496 = filter_out_common_univs us1 us2  in
                (match uu____7496 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____7555 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____7555 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____7558 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____7568 =
                          let uu____7569 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____7570 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____7569
                            uu____7570
                           in
                        UFailed uu____7568))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7594 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7594 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7620 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7620 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____7623 ->
                let uu____7628 =
                  let uu____7629 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____7630 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____7629
                    uu____7630 msg
                   in
                UFailed uu____7628
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____7631,uu____7632) ->
              let uu____7633 =
                let uu____7634 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7635 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7634 uu____7635
                 in
              failwith uu____7633
          | (FStar_Syntax_Syntax.U_unknown ,uu____7636) ->
              let uu____7637 =
                let uu____7638 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7639 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7638 uu____7639
                 in
              failwith uu____7637
          | (uu____7640,FStar_Syntax_Syntax.U_bvar uu____7641) ->
              let uu____7642 =
                let uu____7643 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7644 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7643 uu____7644
                 in
              failwith uu____7642
          | (uu____7645,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____7646 =
                let uu____7647 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7648 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7647 uu____7648
                 in
              failwith uu____7646
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____7672 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____7672
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____7686 = occurs_univ v1 u3  in
              if uu____7686
              then
                let uu____7687 =
                  let uu____7688 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7689 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7688 uu____7689
                   in
                try_umax_components u11 u21 uu____7687
              else
                (let uu____7691 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7691)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____7703 = occurs_univ v1 u3  in
              if uu____7703
              then
                let uu____7704 =
                  let uu____7705 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7706 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7705 uu____7706
                   in
                try_umax_components u11 u21 uu____7704
              else
                (let uu____7708 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7708)
          | (FStar_Syntax_Syntax.U_max uu____7709,uu____7710) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7716 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7716
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____7718,FStar_Syntax_Syntax.U_max uu____7719) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7725 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7725
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____7727,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____7728,FStar_Syntax_Syntax.U_name
             uu____7729) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____7730) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____7731) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7732,FStar_Syntax_Syntax.U_succ
             uu____7733) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7734,FStar_Syntax_Syntax.U_zero
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
      let uu____7834 = bc1  in
      match uu____7834 with
      | (bs1,mk_cod1) ->
          let uu____7878 = bc2  in
          (match uu____7878 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____7989 = aux xs ys  in
                     (match uu____7989 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____8072 =
                       let uu____8079 = mk_cod1 xs  in ([], uu____8079)  in
                     let uu____8082 =
                       let uu____8089 = mk_cod2 ys  in ([], uu____8089)  in
                     (uu____8072, uu____8082)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____8112 'Auu____8113 'Auu____8114 .
    ('Auu____8112,'Auu____8113,'Auu____8114 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___111_8127  ->
    match uu___111_8127 with
    | (uu____8136,uu____8137,[]) -> true
    | uu____8140 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8171 = f  in
      match uu____8171 with
      | (uu____8178,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8179;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8180;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8183;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8184;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8185;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____8237  ->
                 match uu____8237 with
                 | (y,uu____8243) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                FStar_Pervasives_Native.Some
                  ((FStar_List.rev pat_binders), t_res)
            | (uu____8349,[]) ->
                FStar_Pervasives_Native.Some
                  ((FStar_List.rev pat_binders), t_res)
            | ((formal,uu____8381)::formals1,(a,uu____8384)::args2) ->
                let uu____8418 =
                  let uu____8419 = FStar_Syntax_Subst.compress a  in
                  uu____8419.FStar_Syntax_Syntax.n  in
                (match uu____8418 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____8431 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____8431
                     then
                       let uu____8440 =
                         let uu____8443 =
                           FStar_Syntax_Syntax.mk_binder formal  in
                         uu____8443 :: pat_binders  in
                       aux uu____8440 formals1 t_res args2
                     else
                       (let x1 =
                          let uu___139_8446 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___139_8446.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___139_8446.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____8450 =
                            let uu____8451 =
                              let uu____8458 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____8458)  in
                            FStar_Syntax_Syntax.NT uu____8451  in
                          [uu____8450]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        let uu____8465 =
                          let uu____8468 =
                            FStar_Syntax_Syntax.mk_binder
                              (let uu___140_8471 = x1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___140_8471.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___140_8471.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort =
                                   (formal.FStar_Syntax_Syntax.sort)
                               })
                             in
                          uu____8468 :: pat_binders  in
                        aux uu____8465 formals2 t_res1 args2)
                 | uu____8472 ->
                     let uu____8473 =
                       let uu____8476 = FStar_Syntax_Syntax.mk_binder formal
                          in
                       uu____8476 :: pat_binders  in
                     aux uu____8473 formals1 t_res args2)
            | ([],args2) ->
                let uu____8500 =
                  let uu____8513 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____8513  in
                (match uu____8500 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____8558 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____8585 ->
               let uu____8586 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____8586 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let (meet_or_join :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
      FStar_TypeChecker_Env.env ->
        worklist ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Common.prob Prims.list,
            worklist) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    fun ts  ->
      fun env  ->
        fun wl  ->
          let eq_prob t1 t2 wl1 =
            let uu____8697 =
              new_problem wl1 env t1 FStar_TypeChecker_Common.EQ t2
                FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                "join/meet refinements"
               in
            match uu____8697 with
            | (p,wl2) -> ((FStar_TypeChecker_Common.TProb p), wl2)  in
          let pairwise t1 t2 wl1 =
            let uu____8742 = head_matches_delta env () t1 t2  in
            match uu____8742 with
            | (mr,ts1) ->
                (match mr with
                 | MisMatch uu____8783 ->
                     let uu____8792 = eq_prob t1 t2 wl1  in
                     (match uu____8792 with | (p,wl2) -> (t1, [p], wl2))
                 | FullMatch  ->
                     (match ts1 with
                      | FStar_Pervasives_Native.None  -> (t1, [], wl1)
                      | FStar_Pervasives_Native.Some (t11,t21) ->
                          (t11, [], wl1))
                 | HeadMatch  ->
                     let uu____8831 =
                       match ts1 with
                       | FStar_Pervasives_Native.Some (t11,t21) ->
                           let uu____8846 = FStar_Syntax_Subst.compress t11
                              in
                           let uu____8847 = FStar_Syntax_Subst.compress t21
                              in
                           (uu____8846, uu____8847)
                       | FStar_Pervasives_Native.None  ->
                           let uu____8852 = FStar_Syntax_Subst.compress t1
                              in
                           let uu____8853 = FStar_Syntax_Subst.compress t2
                              in
                           (uu____8852, uu____8853)
                        in
                     (match uu____8831 with
                      | (t11,t21) ->
                          let uu____8864 =
                            base_and_refinement_maybe_delta true env t11  in
                          (match uu____8864 with
                           | (t12,p1_opt) ->
                               let uu____8903 =
                                 base_and_refinement_maybe_delta true env t21
                                  in
                               (match uu____8903 with
                                | (t22,p2_opt) ->
                                    let uu____8942 = eq_prob t12 t22 wl1  in
                                    (match uu____8942 with
                                     | (p,wl2) ->
                                         let t =
                                           match (p1_opt, p2_opt) with
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
                                               let uu____9024 =
                                                 op phi11 phi21  in
                                               FStar_Syntax_Util.refine x1
                                                 uu____9024
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
                                               let uu____9066 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               FStar_Syntax_Util.refine x1
                                                 uu____9066
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
                                               let uu____9108 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               FStar_Syntax_Util.refine x1
                                                 uu____9108
                                           | uu____9111 -> t12  in
                                         (t12, [p], wl2))))))
             in
          let rec aux uu____9163 ts1 =
            match uu____9163 with
            | (out,probs,wl1) ->
                (match ts1 with
                 | [] -> (out, probs, wl1)
                 | t::ts2 ->
                     let uu____9214 = pairwise out t wl1  in
                     (match uu____9214 with
                      | (out1,probs',wl2) ->
                          aux (out1, (FStar_List.append probs probs'), wl2)
                            ts2))
             in
          let uu____9240 =
            let uu____9249 = FStar_List.hd ts  in (uu____9249, [], wl)  in
          let uu____9252 = FStar_List.tl ts  in aux uu____9240 uu____9252
  
let (conjoin :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        (FStar_Syntax_Syntax.term,FStar_TypeChecker_Common.prob Prims.list,
          worklist) FStar_Pervasives_Native.tuple3)
  = meet_or_join FStar_Syntax_Util.mk_conj 
let (disjoin :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        (FStar_Syntax_Syntax.term,FStar_TypeChecker_Common.prob Prims.list,
          worklist) FStar_Pervasives_Native.tuple3)
  = meet_or_join FStar_Syntax_Util.mk_disj 
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9542 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9542
       then
         let uu____9543 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9543
       else ());
      (let uu____9545 = next_prob probs  in
       match uu____9545 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___141_9572 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___141_9572.wl_deferred);
               ctr = (uu___141_9572.ctr);
               defer_ok = (uu___141_9572.defer_ok);
               smt_ok = (uu___141_9572.smt_ok);
               tcenv = (uu___141_9572.tcenv);
               wl_implicits = (uu___141_9572.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____9579 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____9579
                then
                  let uu____9580 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____9580
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
                          (let uu___142_9585 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___142_9585.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___142_9585.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___142_9585.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___142_9585.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___142_9585.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___142_9585.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___142_9585.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___142_9585.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___142_9585.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9607 ->
                let uu____9616 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9675  ->
                          match uu____9675 with
                          | (c,uu____9683,uu____9684) -> c < probs.ctr))
                   in
                (match uu____9616 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9725 =
                            let uu____9730 =
                              FStar_List.map
                                (fun uu____9745  ->
                                   match uu____9745 with
                                   | (uu____9756,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9730, (probs.wl_implicits))  in
                          Success uu____9725
                      | uu____9759 ->
                          let uu____9768 =
                            let uu___143_9769 = probs  in
                            let uu____9770 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9789  ->
                                      match uu____9789 with
                                      | (uu____9796,uu____9797,y) -> y))
                               in
                            {
                              attempting = uu____9770;
                              wl_deferred = rest;
                              ctr = (uu___143_9769.ctr);
                              defer_ok = (uu___143_9769.defer_ok);
                              smt_ok = (uu___143_9769.smt_ok);
                              tcenv = (uu___143_9769.tcenv);
                              wl_implicits = (uu___143_9769.wl_implicits)
                            }  in
                          solve env uu____9768))))

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
            let uu____9804 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9804 with
            | USolved wl1 ->
                let uu____9806 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9806
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
                  let uu____9858 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____9858 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9861 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9873;
                  FStar_Syntax_Syntax.vars = uu____9874;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9877;
                  FStar_Syntax_Syntax.vars = uu____9878;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9890,uu____9891) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9898,FStar_Syntax_Syntax.Tm_uinst uu____9899) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9906 -> USolved wl

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
            ((let uu____9916 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____9916
              then
                let uu____9917 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9917 msg
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
          let uu____9925 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____9925 with
          | (this_flex,this_rigid) ->
              let uu____9937 =
                let uu____9938 = FStar_Syntax_Subst.compress this_rigid  in
                uu____9938.FStar_Syntax_Syntax.n  in
              (match uu____9937 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____9959 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____9959
                   then
                     let flex = destruct_flex_t this_flex  in
                     let uu____9961 = quasi_pattern env flex  in
                     (match uu____9961 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env
                            "flex-arrow subtyping, not a quasi pattern"
                            (FStar_TypeChecker_Common.TProb tp)
                      | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                          ((let uu____9979 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____9979
                            then
                              let uu____9980 =
                                FStar_Util.string_of_int
                                  tp.FStar_TypeChecker_Common.pid
                                 in
                              FStar_Util.print1
                                "Trying to solve by imitating arrow:%s\n"
                                uu____9980
                            else ());
                           imitate_arrow (FStar_TypeChecker_Common.TProb tp)
                             env wl flex flex_bs flex_t
                             tp.FStar_TypeChecker_Common.relation this_rigid))
                   else
                     solve env
                       (attempt
                          [FStar_TypeChecker_Common.TProb
                             ((let uu___144_9985 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___144_9985.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___144_9985.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___144_9985.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___144_9985.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___144_9985.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___144_9985.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___144_9985.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___144_9985.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___144_9985.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____9986 ->
                   ((let uu____9988 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____9988
                     then
                       let uu____9989 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____9989
                     else ());
                    (let uu____9991 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____9991 with
                     | (u,_args) ->
                         let uu____10022 =
                           let uu____10023 = FStar_Syntax_Subst.compress u
                              in
                           uu____10023.FStar_Syntax_Syntax.n  in
                         (match uu____10022 with
                          | FStar_Syntax_Syntax.Tm_uvar ctx_uvar ->
                              let equiv1 t =
                                let uu____10033 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____10033 with
                                | (u',uu____10047) ->
                                    let uu____10064 =
                                      let uu____10065 = whnf env u'  in
                                      uu____10065.FStar_Syntax_Syntax.n  in
                                    (match uu____10064 with
                                     | FStar_Syntax_Syntax.Tm_uvar ctx_uvar'
                                         ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____10069 -> false)
                                 in
                              let uu____10070 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___112_10093  ->
                                        match uu___112_10093 with
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
                                             | uu____10102 -> false)
                                        | uu____10105 -> false))
                                 in
                              (match uu____10070 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____10119 = whnf env this_rigid
                                        in
                                     let uu____10120 =
                                       FStar_List.collect
                                         (fun uu___113_10126  ->
                                            match uu___113_10126 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____10132 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____10132]
                                            | uu____10134 -> []) bounds_probs
                                        in
                                     uu____10119 :: uu____10120  in
                                   let uu____10135 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____10135 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____10160 =
                                          let uu____10167 =
                                            destruct_flex_t this_flex  in
                                          match uu____10167 with
                                          | (uu____10174,flex_u,uu____10176)
                                              ->
                                              let bound1 =
                                                let uu____10178 =
                                                  let uu____10179 =
                                                    FStar_Syntax_Subst.compress
                                                      bound
                                                     in
                                                  uu____10179.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____10178 with
                                                | FStar_Syntax_Syntax.Tm_refine
                                                    (x,phi) when
                                                    (tp.FStar_TypeChecker_Common.relation
                                                       =
                                                       FStar_TypeChecker_Common.SUB)
                                                      &&
                                                      (let uu____10189 =
                                                         occurs flex_u
                                                           x.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_Pervasives_Native.snd
                                                         uu____10189)
                                                    ->
                                                    x.FStar_Syntax_Syntax.sort
                                                | uu____10198 -> bound  in
                                              new_problem wl1 env bound1
                                                FStar_TypeChecker_Common.EQ
                                                this_flex
                                                FStar_Pervasives_Native.None
                                                tp.FStar_TypeChecker_Common.loc
                                                (if flip
                                                 then "joining refinements"
                                                 else "meeting refinements")
                                           in
                                        (match uu____10160 with
                                         | (eq_prob,wl2) ->
                                             ((let uu____10207 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "RelCheck")
                                                  in
                                               if uu____10207
                                               then
                                                 let wl' =
                                                   let uu___145_10209 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___145_10209.wl_deferred);
                                                     ctr =
                                                       (uu___145_10209.ctr);
                                                     defer_ok =
                                                       (uu___145_10209.defer_ok);
                                                     smt_ok =
                                                       (uu___145_10209.smt_ok);
                                                     tcenv =
                                                       (uu___145_10209.tcenv);
                                                     wl_implicits =
                                                       (uu___145_10209.wl_implicits)
                                                   }  in
                                                 let uu____10210 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____10210
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10213 =
                                                 solve_t env eq_prob
                                                   (let uu___146_10215 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___146_10215.wl_deferred);
                                                      ctr =
                                                        (uu___146_10215.ctr);
                                                      defer_ok =
                                                        (uu___146_10215.defer_ok);
                                                      smt_ok =
                                                        (uu___146_10215.smt_ok);
                                                      tcenv =
                                                        (uu___146_10215.tcenv);
                                                      wl_implicits =
                                                        (uu___146_10215.wl_implicits)
                                                    })
                                                  in
                                               match uu____10213 with
                                               | Success uu____10216 ->
                                                   let wl3 =
                                                     let uu___147_10222 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___147_10222.wl_deferred);
                                                       ctr =
                                                         (uu___147_10222.ctr);
                                                       defer_ok =
                                                         (uu___147_10222.defer_ok);
                                                       smt_ok =
                                                         (uu___147_10222.smt_ok);
                                                       tcenv =
                                                         (uu___147_10222.tcenv);
                                                       wl_implicits =
                                                         (uu___147_10222.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____10226 =
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
                          | uu____10237 when flip ->
                              let uu____10238 =
                                let uu____10239 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a flex-rigid: %s"
                                  uu____10239
                                 in
                              failwith uu____10238
                          | uu____10240 ->
                              let uu____10241 =
                                let uu____10242 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a rigid-flex: %s"
                                  uu____10242
                                 in
                              failwith uu____10241))))

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
                      (fun uu____10270  ->
                         match uu____10270 with
                         | (x,i) ->
                             let uu____10281 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____10281, i)) bs_lhs
                     in
                  let uu____10282 = lhs  in
                  match uu____10282 with
                  | (uu____10283,u_lhs,uu____10285) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____10398 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____10408 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____10408, univ)
                             in
                          match uu____10398 with
                          | (k,univ) ->
                              let uu____10421 =
                                let uu____10428 =
                                  let uu____10431 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____10431
                                   in
                                copy_uvar u_lhs uu____10428 wl2  in
                              (match uu____10421 with
                               | (uu____10444,u,wl3) ->
                                   let uu____10447 =
                                     let uu____10450 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____10450
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____10447, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____10486 =
                              let uu____10499 =
                                let uu____10508 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____10508 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____10554  ->
                                   fun uu____10555  ->
                                     match (uu____10554, uu____10555) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____10646 =
                                           let uu____10653 =
                                             let uu____10656 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____10656
                                              in
                                           copy_uvar u_lhs uu____10653 wl2
                                            in
                                         (match uu____10646 with
                                          | (uu____10685,t_a,wl3) ->
                                              let uu____10688 =
                                                let uu____10695 =
                                                  let uu____10698 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____10698
                                                   in
                                                copy_uvar u_lhs uu____10695
                                                  wl3
                                                 in
                                              (match uu____10688 with
                                               | (uu____10713,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____10499
                                ([], wl1)
                               in
                            (match uu____10486 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___148_10774 = ct  in
                                   let uu____10775 =
                                     let uu____10778 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____10778
                                      in
                                   let uu____10793 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___148_10774.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___148_10774.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____10775;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____10793;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___148_10774.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___149_10811 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___149_10811.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___149_10811.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____10814 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____10814 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____10868 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____10868 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____10885 =
                                          let uu____10890 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____10890)  in
                                        TERM uu____10885  in
                                      let uu____10891 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____10891 with
                                       | (sub_prob,wl3) ->
                                           let uu____10902 =
                                             let uu____10903 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____10903
                                              in
                                           solve env uu____10902))
                             | (x,imp)::formals2 ->
                                 let uu____10917 =
                                   let uu____10924 =
                                     let uu____10927 =
                                       let uu____10930 =
                                         let uu____10931 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____10931
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____10930
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____10927
                                      in
                                   copy_uvar u_lhs uu____10924 wl1  in
                                 (match uu____10917 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____10955 =
                                          let uu____10958 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____10958
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____10955 t_y
                                         in
                                      let uu____10959 =
                                        let uu____10962 =
                                          let uu____10965 =
                                            let uu____10966 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____10966, imp)  in
                                          [uu____10965]  in
                                        FStar_List.append bs_terms
                                          uu____10962
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____10959 formals2 wl2)
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
              (let uu____11008 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____11008
               then
                 let uu____11009 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____11010 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____11009 (rel_to_string (p_rel orig)) uu____11010
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____11115 = rhs wl1 scope env1 subst1  in
                     (match uu____11115 with
                      | (rhs_prob,wl2) ->
                          ((let uu____11135 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____11135
                            then
                              let uu____11136 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____11136
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___150_11190 = hd1  in
                       let uu____11191 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___150_11190.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___150_11190.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11191
                       }  in
                     let hd21 =
                       let uu___151_11195 = hd2  in
                       let uu____11196 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___151_11195.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___151_11195.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11196
                       }  in
                     let uu____11199 =
                       let uu____11204 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____11204
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____11199 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____11223 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____11223
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____11227 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____11227 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____11282 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____11282
                                  in
                               ((let uu____11294 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11294
                                 then
                                   let uu____11295 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____11296 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____11295
                                     uu____11296
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____11323 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____11352 = aux wl [] env [] bs1 bs2  in
               match uu____11352 with
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
        (let uu____11403 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____11403 wl)

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
              let uu____11417 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____11417 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____11447 = lhs1  in
              match uu____11447 with
              | (uu____11450,ctx_u,uu____11452) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____11458 ->
                        let uu____11459 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____11459 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____11506 = quasi_pattern env1 lhs1  in
              match uu____11506 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____11536) ->
                  let uu____11541 = lhs1  in
                  (match uu____11541 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____11555 = occurs_check ctx_u rhs1  in
                       (match uu____11555 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____11597 =
                                let uu____11604 =
                                  let uu____11605 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____11605
                                   in
                                FStar_Util.Inl uu____11604  in
                              (uu____11597, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____11625 =
                                 let uu____11626 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____11626  in
                               if uu____11625
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____11646 =
                                    let uu____11653 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____11653  in
                                  let uu____11658 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____11646, uu____11658)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____11720  ->
                     match uu____11720 with
                     | (x,i) ->
                         let uu____11731 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____11731, i)) bs_lhs
                 in
              let uu____11732 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____11732 with
              | (rhs_hd,args) ->
                  let uu____11763 = FStar_Util.prefix args  in
                  (match uu____11763 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____11821 = lhs1  in
                       (match uu____11821 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____11825 =
                              let uu____11836 =
                                let uu____11843 =
                                  let uu____11846 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____11846
                                   in
                                copy_uvar u_lhs uu____11843 wl1  in
                              match uu____11836 with
                              | (uu____11873,t_last_arg,wl2) ->
                                  let uu____11876 =
                                    let uu____11883 =
                                      let uu____11886 =
                                        let uu____11893 =
                                          let uu____11900 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____11900]  in
                                        FStar_List.append bs_lhs uu____11893
                                         in
                                      let uu____11917 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____11886
                                        uu____11917
                                       in
                                    copy_uvar u_lhs uu____11883 wl2  in
                                  (match uu____11876 with
                                   | (uu____11930,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____11936 =
                                         let uu____11943 =
                                           let uu____11946 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____11946
                                            in
                                         copy_uvar u_lhs uu____11943 wl3  in
                                       (match uu____11936 with
                                        | (uu____11959,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____11825 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____11983 =
                                     let uu____11984 =
                                       let uu____11989 =
                                         let uu____11990 =
                                           let uu____11993 =
                                             let uu____11998 =
                                               let uu____11999 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____11999]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____11998
                                              in
                                           uu____11993
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____11990
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____11989)  in
                                     TERM uu____11984  in
                                   [uu____11983]  in
                                 let uu____12020 =
                                   let uu____12027 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____12027 with
                                   | (p1,wl3) ->
                                       let uu____12044 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____12044 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____12020 with
                                  | (sub_probs,wl3) ->
                                      let uu____12071 =
                                        let uu____12072 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____12072  in
                                      solve env1 uu____12071))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____12105 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____12105 with
                | (uu____12118,args) ->
                    (match args with | [] -> false | uu____12142 -> true)
                 in
              let is_arrow rhs2 =
                let uu____12157 =
                  let uu____12158 = FStar_Syntax_Subst.compress rhs2  in
                  uu____12158.FStar_Syntax_Syntax.n  in
                match uu____12157 with
                | FStar_Syntax_Syntax.Tm_arrow uu____12161 -> true
                | uu____12174 -> false  in
              let uu____12175 = quasi_pattern env1 lhs1  in
              match uu____12175 with
              | FStar_Pervasives_Native.None  ->
                  let uu____12186 =
                    let uu____12187 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____12187
                     in
                  giveup_or_defer env1 orig1 wl1 uu____12186
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____12194 = is_app rhs1  in
                  if uu____12194
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____12196 = is_arrow rhs1  in
                     if uu____12196
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____12198 =
                          let uu____12199 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____12199
                           in
                        giveup_or_defer env1 orig1 wl1 uu____12198))
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
                let uu____12202 = lhs  in
                (match uu____12202 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____12206 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____12206 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____12221 =
                              let uu____12224 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____12224
                               in
                            FStar_All.pipe_right uu____12221
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____12239 = occurs_check ctx_uv rhs1  in
                          (match uu____12239 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____12261 =
                                   let uu____12262 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____12262
                                    in
                                 giveup_or_defer env orig wl uu____12261
                               else
                                 (let uu____12264 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____12264
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____12269 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____12269
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____12271 =
                                         let uu____12272 =
                                           names_to_string1 fvs2  in
                                         let uu____12273 =
                                           names_to_string1 fvs1  in
                                         let uu____12274 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____12272 uu____12273
                                           uu____12274
                                          in
                                       giveup_or_defer env orig wl
                                         uu____12271)
                                    else first_order orig env wl lhs rhs1))
                      | uu____12280 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____12284 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____12284 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____12307 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____12307
                             | (FStar_Util.Inl msg,uu____12309) ->
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
                  (let uu____12338 =
                     let uu____12355 = quasi_pattern env lhs  in
                     let uu____12362 = quasi_pattern env rhs  in
                     (uu____12355, uu____12362)  in
                   match uu____12338 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____12405 = lhs  in
                       (match uu____12405 with
                        | ({ FStar_Syntax_Syntax.n = uu____12406;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____12408;_},u_lhs,uu____12410)
                            ->
                            let uu____12413 = rhs  in
                            (match uu____12413 with
                             | (uu____12414,u_rhs,uu____12416) ->
                                 let uu____12417 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____12417
                                 then
                                   let uu____12418 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____12418
                                 else
                                   (let uu____12420 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____12420 with
                                    | (sub_prob,wl1) ->
                                        let uu____12431 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____12431 with
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
                                             let uu____12459 =
                                               let uu____12466 =
                                                 let uu____12469 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____12469
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi: lhs="
                                                    (Prims.strcat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.strcat ", rhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))
                                                 wl1 range gamma_w ctx_w
                                                 uu____12466
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____12459 with
                                              | (uu____12472,w,wl2) ->
                                                  let w_app =
                                                    let uu____12478 =
                                                      let uu____12483 =
                                                        FStar_List.map
                                                          (fun uu____12492 
                                                             ->
                                                             match uu____12492
                                                             with
                                                             | (z,uu____12498)
                                                                 ->
                                                                 let uu____12499
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____12499)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____12483
                                                       in
                                                    uu____12478
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____12503 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "RelCheck")
                                                       in
                                                    if uu____12503
                                                    then
                                                      let uu____12504 =
                                                        flex_t_to_string lhs
                                                         in
                                                      let uu____12505 =
                                                        flex_t_to_string rhs
                                                         in
                                                      let uu____12506 =
                                                        let uu____12507 =
                                                          destruct_flex_t w
                                                           in
                                                        flex_t_to_string
                                                          uu____12507
                                                         in
                                                      FStar_Util.print3
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s"
                                                        uu____12504
                                                        uu____12505
                                                        uu____12506
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____12519 =
                                                          let uu____12524 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____12524)
                                                           in
                                                        TERM uu____12519  in
                                                      let uu____12525 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____12525
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____12530 =
                                                             let uu____12535
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
                                                               uu____12535)
                                                              in
                                                           TERM uu____12530
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____12536 =
                                                      let uu____12537 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____12537
                                                       in
                                                    solve env uu____12536)))))))
                   | uu____12538 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12606 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12606 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12637,uu____12638) ->
                    let rec may_relate head3 =
                      let uu____12665 =
                        let uu____12666 = FStar_Syntax_Subst.compress head3
                           in
                        uu____12666.FStar_Syntax_Syntax.n  in
                      match uu____12665 with
                      | FStar_Syntax_Syntax.Tm_name uu____12669 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12670 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12693;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational ;
                            FStar_Syntax_Syntax.fv_qual = uu____12694;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12697;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____12698;
                            FStar_Syntax_Syntax.fv_qual = uu____12699;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____12703,uu____12704) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____12746) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____12752) ->
                          may_relate t
                      | uu____12757 -> false  in
                    let uu____12758 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____12758
                    then
                      let uu____12759 =
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
                                 let uu____12791 =
                                   let uu____12792 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____12792 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____12791
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____12797 = has_type_guard t1 t2  in
                             (uu____12797, wl1)
                           else
                             (let uu____12803 = has_type_guard t2 t1  in
                              (uu____12803, wl1)))
                         in
                      (match uu____12759 with
                       | (guard,wl2) ->
                           let uu____12810 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____12810)
                    else
                      (let uu____12812 =
                         let uu____12813 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12814 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____12813 uu____12814
                          in
                       giveup env1 uu____12812 orig)
                | (uu____12815,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___152_12829 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___152_12829.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___152_12829.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___152_12829.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___152_12829.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___152_12829.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___152_12829.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___152_12829.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___152_12829.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____12830,FStar_Pervasives_Native.None ) ->
                    ((let uu____12842 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12842
                      then
                        let uu____12843 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____12844 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____12845 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____12846 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____12843
                          uu____12844 uu____12845 uu____12846
                      else ());
                     (let uu____12848 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____12848 with
                      | (head11,args1) ->
                          let uu____12879 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____12879 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____12927 =
                                   let uu____12928 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____12929 = args_to_string args1  in
                                   let uu____12930 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____12931 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____12928 uu____12929 uu____12930
                                     uu____12931
                                    in
                                 giveup env1 uu____12927 orig
                               else
                                 (let uu____12933 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____12940 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____12940 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____12933
                                  then
                                    let uu____12941 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____12941 with
                                    | USolved wl2 ->
                                        let uu____12943 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____12943
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____12947 =
                                       base_and_refinement env1 t1  in
                                     match uu____12947 with
                                     | (base1,refinement1) ->
                                         let uu____12972 =
                                           base_and_refinement env1 t2  in
                                         (match uu____12972 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____13029 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____13029 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____13033 =
                                                          FStar_List.fold_right2
                                                            (fun uu____13066 
                                                               ->
                                                               fun
                                                                 uu____13067 
                                                                 ->
                                                                 fun
                                                                   uu____13068
                                                                    ->
                                                                   match 
                                                                    (uu____13066,
                                                                    uu____13067,
                                                                    uu____13068)
                                                                   with
                                                                   | 
                                                                   ((a,uu____13104),
                                                                    (a',uu____13106),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____13127
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____13127
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
                                                        (match uu____13033
                                                         with
                                                         | (subprobs,wl3) ->
                                                             let formula =
                                                               let uu____13157
                                                                 =
                                                                 FStar_List.map
                                                                   (fun p  ->
                                                                    p_guard p)
                                                                   subprobs
                                                                  in
                                                               FStar_Syntax_Util.mk_conj_l
                                                                 uu____13157
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
                                               | uu____13165 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___153_13205 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___153_13205.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____13208 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____13208
          then
            let uu____13209 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____13209
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____13214 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "RelCheck")
                 in
              if uu____13214
              then
                let uu____13215 = FStar_Syntax_Print.tag_of_term t1  in
                let uu____13216 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____13217 = prob_to_string env orig  in
                FStar_Util.print3 "Attempting (%s - %s)\n%s\n" uu____13215
                  uu____13216 uu____13217
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____13220,uu____13221) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____13246,FStar_Syntax_Syntax.Tm_delayed uu____13247) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____13272,uu____13273) ->
                  let uu____13300 =
                    let uu___154_13301 = problem  in
                    let uu____13302 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___154_13301.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____13302;
                      FStar_TypeChecker_Common.relation =
                        (uu___154_13301.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___154_13301.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___154_13301.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___154_13301.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___154_13301.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___154_13301.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___154_13301.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___154_13301.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13300 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____13303,uu____13304) ->
                  let uu____13311 =
                    let uu___155_13312 = problem  in
                    let uu____13313 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___155_13312.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____13313;
                      FStar_TypeChecker_Common.relation =
                        (uu___155_13312.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___155_13312.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___155_13312.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___155_13312.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___155_13312.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___155_13312.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___155_13312.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___155_13312.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13311 wl
              | (uu____13314,FStar_Syntax_Syntax.Tm_ascribed uu____13315) ->
                  let uu____13342 =
                    let uu___156_13343 = problem  in
                    let uu____13344 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___156_13343.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___156_13343.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___156_13343.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____13344;
                      FStar_TypeChecker_Common.element =
                        (uu___156_13343.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___156_13343.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___156_13343.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___156_13343.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___156_13343.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___156_13343.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13342 wl
              | (uu____13345,FStar_Syntax_Syntax.Tm_meta uu____13346) ->
                  let uu____13353 =
                    let uu___157_13354 = problem  in
                    let uu____13355 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___157_13354.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___157_13354.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___157_13354.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____13355;
                      FStar_TypeChecker_Common.element =
                        (uu___157_13354.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___157_13354.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___157_13354.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___157_13354.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___157_13354.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___157_13354.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13353 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____13357),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____13359)) ->
                  let uu____13368 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____13368
              | (FStar_Syntax_Syntax.Tm_bvar uu____13369,uu____13370) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____13371,FStar_Syntax_Syntax.Tm_bvar uu____13372) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___114_13431 =
                    match uu___114_13431 with
                    | [] -> c
                    | bs ->
                        let uu____13453 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____13453
                     in
                  let uu____13462 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____13462 with
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
                                    let uu____13585 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____13585
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
                  let mk_t t l uu___115_13660 =
                    match uu___115_13660 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____13694 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____13694 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____13813 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____13814 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____13813
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____13814 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____13815,uu____13816) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____13843 -> true
                    | uu____13860 -> false  in
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
                      (let uu____13903 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___158_13911 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___158_13911.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___158_13911.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___158_13911.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___158_13911.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___158_13911.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___158_13911.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___158_13911.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___158_13911.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___158_13911.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___158_13911.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___158_13911.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___158_13911.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___158_13911.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___158_13911.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___158_13911.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___158_13911.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___158_13911.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___158_13911.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___158_13911.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___158_13911.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___158_13911.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___158_13911.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___158_13911.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___158_13911.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___158_13911.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___158_13911.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___158_13911.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___158_13911.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___158_13911.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___158_13911.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___158_13911.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___158_13911.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___158_13911.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___158_13911.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___158_13911.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____13903 with
                       | (uu____13914,ty,uu____13916) ->
                           let uu____13917 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____13917)
                     in
                  let uu____13918 =
                    let uu____13931 = maybe_eta t1  in
                    let uu____13936 = maybe_eta t2  in
                    (uu____13931, uu____13936)  in
                  (match uu____13918 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___159_13960 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___159_13960.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___159_13960.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___159_13960.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___159_13960.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___159_13960.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___159_13960.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___159_13960.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___159_13960.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____13971 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____13971
                       then
                         let uu____13972 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____13972 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___160_13981 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_13981.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___160_13981.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_13981.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_13981.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___160_13981.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_13981.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_13981.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_13981.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____13993 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____13993
                       then
                         let uu____13994 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____13994 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___160_14003 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_14003.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___160_14003.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_14003.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_14003.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___160_14003.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_14003.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_14003.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_14003.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____14005 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____14018,FStar_Syntax_Syntax.Tm_abs uu____14019) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____14046 -> true
                    | uu____14063 -> false  in
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
                      (let uu____14106 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___158_14114 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___158_14114.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___158_14114.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___158_14114.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___158_14114.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___158_14114.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___158_14114.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___158_14114.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___158_14114.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___158_14114.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___158_14114.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___158_14114.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___158_14114.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___158_14114.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___158_14114.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___158_14114.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___158_14114.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___158_14114.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___158_14114.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___158_14114.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___158_14114.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___158_14114.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___158_14114.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___158_14114.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___158_14114.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___158_14114.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___158_14114.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___158_14114.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___158_14114.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___158_14114.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___158_14114.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___158_14114.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___158_14114.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___158_14114.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___158_14114.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___158_14114.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____14106 with
                       | (uu____14117,ty,uu____14119) ->
                           let uu____14120 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____14120)
                     in
                  let uu____14121 =
                    let uu____14134 = maybe_eta t1  in
                    let uu____14139 = maybe_eta t2  in
                    (uu____14134, uu____14139)  in
                  (match uu____14121 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___159_14163 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___159_14163.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___159_14163.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___159_14163.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___159_14163.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___159_14163.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___159_14163.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___159_14163.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___159_14163.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____14174 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14174
                       then
                         let uu____14175 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14175 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___160_14184 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_14184.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___160_14184.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_14184.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_14184.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___160_14184.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_14184.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_14184.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_14184.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____14196 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14196
                       then
                         let uu____14197 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14197 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___160_14206 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___160_14206.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___160_14206.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___160_14206.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___160_14206.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___160_14206.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___160_14206.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___160_14206.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___160_14206.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____14208 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____14236 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____14236) &&
                       (let uu____14240 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____14240))
                      &&
                      (let uu____14247 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____14247 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___116_14259 =
                             match uu___116_14259 with
                             | FStar_Syntax_Syntax.Delta_constant  -> true
                             | FStar_Syntax_Syntax.Delta_defined_at_level
                                 uu____14260 -> true
                             | uu____14261 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____14262 -> false)
                     in
                  let uu____14263 = as_refinement should_delta env wl t1  in
                  (match uu____14263 with
                   | (x11,phi1) ->
                       let uu____14276 = as_refinement should_delta env wl t2
                          in
                       (match uu____14276 with
                        | (x21,phi21) ->
                            let uu____14289 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____14289 with
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
                                   let uu____14355 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____14355
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____14367 =
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
                                   let uu____14378 =
                                     let uu____14383 =
                                       let uu____14390 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____14390]  in
                                     mk_t_problem wl1 uu____14383 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____14378 with
                                    | (ref_prob,wl2) ->
                                        let uu____14405 =
                                          solve env1
                                            (let uu___161_14407 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___161_14407.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___161_14407.smt_ok);
                                               tcenv = (uu___161_14407.tcenv);
                                               wl_implicits =
                                                 (uu___161_14407.wl_implicits)
                                             })
                                           in
                                        (match uu____14405 with
                                         | Failed uu____14414 -> fallback ()
                                         | Success uu____14419 ->
                                             let guard =
                                               let uu____14427 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____14427
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___162_14436 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___162_14436.attempting);
                                                 wl_deferred =
                                                   (uu___162_14436.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___162_14436.defer_ok);
                                                 smt_ok =
                                                   (uu___162_14436.smt_ok);
                                                 tcenv =
                                                   (uu___162_14436.tcenv);
                                                 wl_implicits =
                                                   (uu___162_14436.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____14438,FStar_Syntax_Syntax.Tm_uvar uu____14439) ->
                  let uu____14440 = destruct_flex_t t1  in
                  let uu____14441 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14440 uu____14441
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14442;
                    FStar_Syntax_Syntax.pos = uu____14443;
                    FStar_Syntax_Syntax.vars = uu____14444;_},uu____14445),FStar_Syntax_Syntax.Tm_uvar
                 uu____14446) ->
                  let uu____14467 = destruct_flex_t t1  in
                  let uu____14468 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14467 uu____14468
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____14469,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14470;
                    FStar_Syntax_Syntax.pos = uu____14471;
                    FStar_Syntax_Syntax.vars = uu____14472;_},uu____14473))
                  ->
                  let uu____14494 = destruct_flex_t t1  in
                  let uu____14495 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14494 uu____14495
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14496;
                    FStar_Syntax_Syntax.pos = uu____14497;
                    FStar_Syntax_Syntax.vars = uu____14498;_},uu____14499),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14500;
                    FStar_Syntax_Syntax.pos = uu____14501;
                    FStar_Syntax_Syntax.vars = uu____14502;_},uu____14503))
                  ->
                  let uu____14544 = destruct_flex_t t1  in
                  let uu____14545 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14544 uu____14545
              | (FStar_Syntax_Syntax.Tm_uvar uu____14546,uu____14547) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____14548 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____14548 t2
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14549;
                    FStar_Syntax_Syntax.pos = uu____14550;
                    FStar_Syntax_Syntax.vars = uu____14551;_},uu____14552),uu____14553)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____14574 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____14574 t2
              | (uu____14575,FStar_Syntax_Syntax.Tm_uvar uu____14576) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____14577,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14578;
                    FStar_Syntax_Syntax.pos = uu____14579;
                    FStar_Syntax_Syntax.vars = uu____14580;_},uu____14581))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____14602,FStar_Syntax_Syntax.Tm_arrow uu____14603) ->
                  solve_t' env
                    (let uu___163_14617 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___163_14617.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___163_14617.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___163_14617.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___163_14617.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___163_14617.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___163_14617.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___163_14617.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___163_14617.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___163_14617.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14618;
                    FStar_Syntax_Syntax.pos = uu____14619;
                    FStar_Syntax_Syntax.vars = uu____14620;_},uu____14621),FStar_Syntax_Syntax.Tm_arrow
                 uu____14622) ->
                  solve_t' env
                    (let uu___163_14656 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___163_14656.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___163_14656.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___163_14656.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___163_14656.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___163_14656.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___163_14656.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___163_14656.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___163_14656.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___163_14656.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____14657,FStar_Syntax_Syntax.Tm_uvar uu____14658) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____14659,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14660;
                    FStar_Syntax_Syntax.pos = uu____14661;
                    FStar_Syntax_Syntax.vars = uu____14662;_},uu____14663))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____14684,uu____14685) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14686;
                    FStar_Syntax_Syntax.pos = uu____14687;
                    FStar_Syntax_Syntax.vars = uu____14688;_},uu____14689),uu____14690)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____14711,uu____14712) ->
                  let t21 =
                    let uu____14720 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____14720  in
                  solve_t env
                    (let uu___164_14746 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___164_14746.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___164_14746.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___164_14746.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___164_14746.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___164_14746.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___164_14746.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___164_14746.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___164_14746.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___164_14746.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____14747,FStar_Syntax_Syntax.Tm_refine uu____14748) ->
                  let t11 =
                    let uu____14756 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____14756  in
                  solve_t env
                    (let uu___165_14782 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_14782.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___165_14782.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___165_14782.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___165_14782.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_14782.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___165_14782.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_14782.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_14782.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_14782.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____14859 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____14859 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____15080 = br1  in
                             (match uu____15080 with
                              | (p1,w1,uu____15105) ->
                                  let uu____15122 = br2  in
                                  (match uu____15122 with
                                   | (p2,w2,uu____15141) ->
                                       let uu____15146 =
                                         let uu____15147 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____15147  in
                                       if uu____15146
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____15163 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____15163 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____15196 = br2  in
                                              (match uu____15196 with
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
                                                     let uu____15231 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____15231
                                                      in
                                                   let uu____15242 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____15265,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____15282) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____15325 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____15325
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____15242
                                                     (fun uu____15367  ->
                                                        match uu____15367
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____15388 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____15388
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____15403
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____15403
                                                                   (fun
                                                                    uu____15427
                                                                     ->
                                                                    match uu____15427
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
                         | uu____15512 -> FStar_Pervasives_Native.None  in
                       let uu____15549 = solve_branches wl1 brs1 brs2  in
                       (match uu____15549 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____15580,uu____15581) ->
                  let head1 =
                    let uu____15605 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15605
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____15639 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____15639
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____15673 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____15673
                    then
                      let uu____15674 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____15675 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____15676 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____15674 uu____15675 uu____15676
                    else ());
                   (let uu____15678 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____15678
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____15685 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____15685
                       then
                         let uu____15686 =
                           let uu____15693 =
                             let uu____15694 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____15694 = FStar_Syntax_Util.Equal  in
                           if uu____15693
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____15704 = mk_eq2 wl orig t1 t2  in
                              match uu____15704 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____15686 with
                         | (guard,wl1) ->
                             let uu____15725 = solve_prob orig guard [] wl1
                                in
                             solve env uu____15725
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____15728,uu____15729) ->
                  let head1 =
                    let uu____15737 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15737
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____15771 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____15771
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____15805 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____15805
                    then
                      let uu____15806 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____15807 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____15808 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____15806 uu____15807 uu____15808
                    else ());
                   (let uu____15810 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____15810
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____15817 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____15817
                       then
                         let uu____15818 =
                           let uu____15825 =
                             let uu____15826 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____15826 = FStar_Syntax_Util.Equal  in
                           if uu____15825
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____15836 = mk_eq2 wl orig t1 t2  in
                              match uu____15836 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____15818 with
                         | (guard,wl1) ->
                             let uu____15857 = solve_prob orig guard [] wl1
                                in
                             solve env uu____15857
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____15860,uu____15861) ->
                  let head1 =
                    let uu____15863 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15863
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____15897 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____15897
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____15931 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____15931
                    then
                      let uu____15932 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____15933 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____15934 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____15932 uu____15933 uu____15934
                    else ());
                   (let uu____15936 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____15936
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____15943 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____15943
                       then
                         let uu____15944 =
                           let uu____15951 =
                             let uu____15952 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____15952 = FStar_Syntax_Util.Equal  in
                           if uu____15951
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____15962 = mk_eq2 wl orig t1 t2  in
                              match uu____15962 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____15944 with
                         | (guard,wl1) ->
                             let uu____15983 = solve_prob orig guard [] wl1
                                in
                             solve env uu____15983
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____15986,uu____15987) ->
                  let head1 =
                    let uu____15989 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15989
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16023 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16023
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16057 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16057
                    then
                      let uu____16058 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16059 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16060 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16058 uu____16059 uu____16060
                    else ());
                   (let uu____16062 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16062
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16069 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16069
                       then
                         let uu____16070 =
                           let uu____16077 =
                             let uu____16078 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16078 = FStar_Syntax_Util.Equal  in
                           if uu____16077
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16088 = mk_eq2 wl orig t1 t2  in
                              match uu____16088 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16070 with
                         | (guard,wl1) ->
                             let uu____16109 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16109
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____16112,uu____16113) ->
                  let head1 =
                    let uu____16115 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16115
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16149 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16149
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16183 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16183
                    then
                      let uu____16184 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16185 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16186 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16184 uu____16185 uu____16186
                    else ());
                   (let uu____16188 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16188
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16195 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16195
                       then
                         let uu____16196 =
                           let uu____16203 =
                             let uu____16204 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16204 = FStar_Syntax_Util.Equal  in
                           if uu____16203
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16214 = mk_eq2 wl orig t1 t2  in
                              match uu____16214 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16196 with
                         | (guard,wl1) ->
                             let uu____16235 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16235
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____16238,uu____16239) ->
                  let head1 =
                    let uu____16255 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16255
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16289 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16289
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16323 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16323
                    then
                      let uu____16324 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16325 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16326 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16324 uu____16325 uu____16326
                    else ());
                   (let uu____16328 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16328
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16335 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16335
                       then
                         let uu____16336 =
                           let uu____16343 =
                             let uu____16344 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16344 = FStar_Syntax_Util.Equal  in
                           if uu____16343
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16354 = mk_eq2 wl orig t1 t2  in
                              match uu____16354 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16336 with
                         | (guard,wl1) ->
                             let uu____16375 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16375
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16378,FStar_Syntax_Syntax.Tm_match uu____16379) ->
                  let head1 =
                    let uu____16403 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16403
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16437 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16437
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16471 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16471
                    then
                      let uu____16472 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16473 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16474 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16472 uu____16473 uu____16474
                    else ());
                   (let uu____16476 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16476
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16483 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16483
                       then
                         let uu____16484 =
                           let uu____16491 =
                             let uu____16492 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16492 = FStar_Syntax_Util.Equal  in
                           if uu____16491
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16502 = mk_eq2 wl orig t1 t2  in
                              match uu____16502 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16484 with
                         | (guard,wl1) ->
                             let uu____16523 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16523
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16526,FStar_Syntax_Syntax.Tm_uinst uu____16527) ->
                  let head1 =
                    let uu____16535 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16535
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16569 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16569
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16603 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16603
                    then
                      let uu____16604 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16605 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16606 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16604 uu____16605 uu____16606
                    else ());
                   (let uu____16608 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16608
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16615 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16615
                       then
                         let uu____16616 =
                           let uu____16623 =
                             let uu____16624 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16624 = FStar_Syntax_Util.Equal  in
                           if uu____16623
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16634 = mk_eq2 wl orig t1 t2  in
                              match uu____16634 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16616 with
                         | (guard,wl1) ->
                             let uu____16655 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16655
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16658,FStar_Syntax_Syntax.Tm_name uu____16659) ->
                  let head1 =
                    let uu____16661 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16661
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16695 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16695
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16729 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16729
                    then
                      let uu____16730 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16731 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16732 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16730 uu____16731 uu____16732
                    else ());
                   (let uu____16734 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16734
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16741 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16741
                       then
                         let uu____16742 =
                           let uu____16749 =
                             let uu____16750 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16750 = FStar_Syntax_Util.Equal  in
                           if uu____16749
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16760 = mk_eq2 wl orig t1 t2  in
                              match uu____16760 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16742 with
                         | (guard,wl1) ->
                             let uu____16781 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16781
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16784,FStar_Syntax_Syntax.Tm_constant uu____16785) ->
                  let head1 =
                    let uu____16787 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16787
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16821 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16821
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16855 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16855
                    then
                      let uu____16856 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16857 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16858 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16856 uu____16857 uu____16858
                    else ());
                   (let uu____16860 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16860
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16867 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16867
                       then
                         let uu____16868 =
                           let uu____16875 =
                             let uu____16876 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16876 = FStar_Syntax_Util.Equal  in
                           if uu____16875
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16886 = mk_eq2 wl orig t1 t2  in
                              match uu____16886 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16868 with
                         | (guard,wl1) ->
                             let uu____16907 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16907
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16910,FStar_Syntax_Syntax.Tm_fvar uu____16911) ->
                  let head1 =
                    let uu____16913 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16913
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16947 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16947
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16981 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16981
                    then
                      let uu____16982 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16983 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16984 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16982 uu____16983 uu____16984
                    else ());
                   (let uu____16986 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16986
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16993 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16993
                       then
                         let uu____16994 =
                           let uu____17001 =
                             let uu____17002 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17002 = FStar_Syntax_Util.Equal  in
                           if uu____17001
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17012 = mk_eq2 wl orig t1 t2  in
                              match uu____17012 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16994 with
                         | (guard,wl1) ->
                             let uu____17033 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17033
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17036,FStar_Syntax_Syntax.Tm_app uu____17037) ->
                  let head1 =
                    let uu____17053 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17053
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17087 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17087
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17121 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17121
                    then
                      let uu____17122 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17123 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17124 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17122 uu____17123 uu____17124
                    else ());
                   (let uu____17126 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17126
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17133 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17133
                       then
                         let uu____17134 =
                           let uu____17141 =
                             let uu____17142 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17142 = FStar_Syntax_Util.Equal  in
                           if uu____17141
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17152 = mk_eq2 wl orig t1 t2  in
                              match uu____17152 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17134 with
                         | (guard,wl1) ->
                             let uu____17173 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17173
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____17176,FStar_Syntax_Syntax.Tm_let uu____17177) ->
                  let uu____17202 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____17202
                  then
                    let uu____17203 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____17203
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____17205,uu____17206) ->
                  let uu____17219 =
                    let uu____17224 =
                      let uu____17225 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____17226 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____17227 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____17228 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____17225 uu____17226 uu____17227 uu____17228
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____17224)
                     in
                  FStar_Errors.raise_error uu____17219
                    t1.FStar_Syntax_Syntax.pos
              | (uu____17229,FStar_Syntax_Syntax.Tm_let uu____17230) ->
                  let uu____17243 =
                    let uu____17248 =
                      let uu____17249 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____17250 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____17251 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____17252 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____17249 uu____17250 uu____17251 uu____17252
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____17248)
                     in
                  FStar_Errors.raise_error uu____17243
                    t1.FStar_Syntax_Syntax.pos
              | uu____17253 -> giveup env "head tag mismatch" orig))))

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
          (let uu____17312 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____17312
           then
             let uu____17313 =
               let uu____17314 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____17314  in
             let uu____17315 =
               let uu____17316 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____17316  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____17313 uu____17315
           else ());
          (let uu____17318 =
             let uu____17319 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____17319  in
           if uu____17318
           then
             let uu____17320 =
               let uu____17321 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____17322 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____17321 uu____17322
                in
             giveup env uu____17320 orig
           else
             (let uu____17324 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____17324 with
              | (ret_sub_prob,wl1) ->
                  let uu____17331 =
                    FStar_List.fold_right2
                      (fun uu____17364  ->
                         fun uu____17365  ->
                           fun uu____17366  ->
                             match (uu____17364, uu____17365, uu____17366)
                             with
                             | ((a1,uu____17402),(a2,uu____17404),(arg_sub_probs,wl2))
                                 ->
                                 let uu____17425 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____17425 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____17331 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____17454 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____17454  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____17484 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____17487)::[] -> wp1
              | uu____17504 ->
                  let uu____17513 =
                    let uu____17514 =
                      let uu____17515 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____17515  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____17514
                     in
                  failwith uu____17513
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____17521 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____17521]
              | x -> x  in
            let uu____17523 =
              let uu____17532 =
                let uu____17539 =
                  let uu____17540 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____17540 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____17539  in
              [uu____17532]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____17523;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____17553 = lift_c1 ()  in solve_eq uu____17553 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_17559  ->
                       match uu___117_17559 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____17560 -> false))
                in
             let uu____17561 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____17595)::uu____17596,(wp2,uu____17598)::uu____17599)
                   -> (wp1, wp2)
               | uu____17656 ->
                   let uu____17677 =
                     let uu____17682 =
                       let uu____17683 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____17684 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____17683 uu____17684
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____17682)
                      in
                   FStar_Errors.raise_error uu____17677
                     env.FStar_TypeChecker_Env.range
                in
             match uu____17561 with
             | (wpc1,wpc2) ->
                 let uu____17703 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____17703
                 then
                   let uu____17706 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____17706 wl
                 else
                   (let uu____17708 =
                      let uu____17715 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____17715  in
                    match uu____17708 with
                    | (c2_decl,qualifiers) ->
                        let uu____17736 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____17736
                        then
                          let c1_repr =
                            let uu____17740 =
                              let uu____17741 =
                                let uu____17742 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____17742  in
                              let uu____17743 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____17741 uu____17743
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____17740
                             in
                          let c2_repr =
                            let uu____17745 =
                              let uu____17746 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____17747 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____17746 uu____17747
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____17745
                             in
                          let uu____17748 =
                            let uu____17753 =
                              let uu____17754 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____17755 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____17754 uu____17755
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____17753
                             in
                          (match uu____17748 with
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
                                 ((let uu____17769 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____17769
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____17772 =
                                     let uu____17779 =
                                       let uu____17780 =
                                         let uu____17795 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____17798 =
                                           let uu____17807 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____17814 =
                                             let uu____17823 =
                                               let uu____17830 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____17830
                                                in
                                             [uu____17823]  in
                                           uu____17807 :: uu____17814  in
                                         (uu____17795, uu____17798)  in
                                       FStar_Syntax_Syntax.Tm_app uu____17780
                                        in
                                     FStar_Syntax_Syntax.mk uu____17779  in
                                   uu____17772 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____17871 =
                                    let uu____17878 =
                                      let uu____17879 =
                                        let uu____17894 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____17897 =
                                          let uu____17906 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____17913 =
                                            let uu____17922 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____17929 =
                                              let uu____17938 =
                                                let uu____17945 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____17945
                                                 in
                                              [uu____17938]  in
                                            uu____17922 :: uu____17929  in
                                          uu____17906 :: uu____17913  in
                                        (uu____17894, uu____17897)  in
                                      FStar_Syntax_Syntax.Tm_app uu____17879
                                       in
                                    FStar_Syntax_Syntax.mk uu____17878  in
                                  uu____17871 FStar_Pervasives_Native.None r)
                              in
                           let uu____17989 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____17989 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____17997 =
                                   let uu____18000 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____18000
                                    in
                                 solve_prob orig uu____17997 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____18003 = FStar_Util.physical_equality c1 c2  in
        if uu____18003
        then
          let uu____18004 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____18004
        else
          ((let uu____18007 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____18007
            then
              let uu____18008 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____18009 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____18008
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____18009
            else ());
           (let uu____18011 =
              let uu____18020 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____18023 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____18020, uu____18023)  in
            match uu____18011 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18041),FStar_Syntax_Syntax.Total
                    (t2,uu____18043)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____18060 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18060 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____18061,FStar_Syntax_Syntax.Total uu____18062) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18080),FStar_Syntax_Syntax.Total
                    (t2,uu____18082)) ->
                     let uu____18099 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18099 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18101),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18103)) ->
                     let uu____18120 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18120 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18122),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18124)) ->
                     let uu____18141 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18141 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____18142,FStar_Syntax_Syntax.Comp uu____18143) ->
                     let uu____18152 =
                       let uu___166_18155 = problem  in
                       let uu____18158 =
                         let uu____18159 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18159
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_18155.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18158;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_18155.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_18155.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_18155.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_18155.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___166_18155.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_18155.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_18155.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_18155.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18152 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____18160,FStar_Syntax_Syntax.Comp uu____18161) ->
                     let uu____18170 =
                       let uu___166_18173 = problem  in
                       let uu____18176 =
                         let uu____18177 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18177
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_18173.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18176;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_18173.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_18173.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_18173.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_18173.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___166_18173.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_18173.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_18173.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_18173.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18170 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18178,FStar_Syntax_Syntax.GTotal uu____18179) ->
                     let uu____18188 =
                       let uu___167_18191 = problem  in
                       let uu____18194 =
                         let uu____18195 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18195
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_18191.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_18191.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_18191.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18194;
                         FStar_TypeChecker_Common.element =
                           (uu___167_18191.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_18191.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___167_18191.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_18191.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_18191.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_18191.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18188 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18196,FStar_Syntax_Syntax.Total uu____18197) ->
                     let uu____18206 =
                       let uu___167_18209 = problem  in
                       let uu____18212 =
                         let uu____18213 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18213
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_18209.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_18209.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_18209.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18212;
                         FStar_TypeChecker_Common.element =
                           (uu___167_18209.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_18209.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___167_18209.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_18209.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_18209.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_18209.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18206 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18214,FStar_Syntax_Syntax.Comp uu____18215) ->
                     let uu____18216 =
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
                     if uu____18216
                     then
                       let uu____18217 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____18217 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____18221 =
                            let uu____18226 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____18226
                            then (c1_comp, c2_comp)
                            else
                              (let uu____18232 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____18233 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____18232, uu____18233))
                             in
                          match uu____18221 with
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
                           (let uu____18240 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____18240
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____18242 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____18242 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____18245 =
                                  let uu____18246 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____18247 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____18246 uu____18247
                                   in
                                giveup env uu____18245 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____18254 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____18287  ->
              match uu____18287 with
              | (uu____18298,tm,uu____18300,uu____18301,uu____18302) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____18254 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____18335 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____18335 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____18353 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____18381  ->
                match uu____18381 with
                | (u1,u2) ->
                    let uu____18388 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____18389 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____18388 uu____18389))
         in
      FStar_All.pipe_right uu____18353 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____18416,[])) -> "{}"
      | uu____18441 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____18464 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____18464
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____18467 =
              FStar_List.map
                (fun uu____18477  ->
                   match uu____18477 with
                   | (uu____18482,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____18467 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____18487 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____18487 imps
  
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
                  let uu____18540 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ExplainRel")
                     in
                  if uu____18540
                  then
                    let uu____18541 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____18542 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____18541
                      (rel_to_string rel) uu____18542
                  else "TOP"  in
                let uu____18544 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____18544 with
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
              let uu____18601 =
                let uu____18604 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____18604
                 in
              FStar_Syntax_Syntax.new_bv uu____18601 t1  in
            let uu____18607 =
              let uu____18612 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____18612
               in
            match uu____18607 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____18668 = FStar_Options.eager_inference ()  in
          if uu____18668
          then
            let uu___168_18669 = probs  in
            {
              attempting = (uu___168_18669.attempting);
              wl_deferred = (uu___168_18669.wl_deferred);
              ctr = (uu___168_18669.ctr);
              defer_ok = false;
              smt_ok = (uu___168_18669.smt_ok);
              tcenv = (uu___168_18669.tcenv);
              wl_implicits = (uu___168_18669.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____18689 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____18689
              then
                let uu____18690 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____18690
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
          ((let uu____18712 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____18712
            then
              let uu____18713 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____18713
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____18717 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____18717
             then
               let uu____18718 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____18718
             else ());
            (let f2 =
               let uu____18721 =
                 let uu____18722 = FStar_Syntax_Util.unmeta f1  in
                 uu____18722.FStar_Syntax_Syntax.n  in
               match uu____18721 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____18726 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___169_18727 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___169_18727.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___169_18727.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___169_18727.FStar_TypeChecker_Env.implicits)
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
            let uu____18841 =
              let uu____18842 =
                let uu____18843 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____18843;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____18842  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____18841
  
let with_guard_no_simp :
  'Auu____18858 .
    'Auu____18858 ->
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
            let uu____18881 =
              let uu____18882 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____18882;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____18881
  
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
          (let uu____18922 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____18922
           then
             let uu____18923 = FStar_Syntax_Print.term_to_string t1  in
             let uu____18924 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____18923
               uu____18924
           else ());
          (let uu____18926 =
             let uu____18931 = empty_worklist env  in
             let uu____18932 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____18931 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____18932
              in
           match uu____18926 with
           | (prob,wl) ->
               let g =
                 let uu____18940 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____18960  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____18940  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____19004 = try_teq true env t1 t2  in
        match uu____19004 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____19008 = FStar_TypeChecker_Env.get_range env  in
              let uu____19009 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____19008 uu____19009);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____19016 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____19016
              then
                let uu____19017 = FStar_Syntax_Print.term_to_string t1  in
                let uu____19018 = FStar_Syntax_Print.term_to_string t2  in
                let uu____19019 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____19017
                  uu____19018 uu____19019
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
          let uu____19041 = FStar_TypeChecker_Env.get_range env  in
          let uu____19042 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____19041 uu____19042
  
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
        (let uu____19067 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____19067
         then
           let uu____19068 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____19069 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____19068 uu____19069
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____19072 =
           let uu____19079 = empty_worklist env  in
           let uu____19080 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____19079 env c1 rel c2 FStar_Pervasives_Native.None
             uu____19080 "sub_comp"
            in
         match uu____19072 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____19090 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____19110  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____19090)
  
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
      fun uu____19165  ->
        match uu____19165 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____19208 =
                 let uu____19213 =
                   let uu____19214 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____19215 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____19214 uu____19215
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____19213)  in
               let uu____19216 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____19208 uu____19216)
               in
            let equiv1 v1 v' =
              let uu____19228 =
                let uu____19233 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____19234 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____19233, uu____19234)  in
              match uu____19228 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____19253 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____19283 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____19283 with
                      | FStar_Syntax_Syntax.U_unif uu____19290 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____19319  ->
                                    match uu____19319 with
                                    | (u,v') ->
                                        let uu____19328 = equiv1 v1 v'  in
                                        if uu____19328
                                        then
                                          let uu____19331 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____19331 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____19347 -> []))
               in
            let uu____19352 =
              let wl =
                let uu___170_19356 = empty_worklist env  in
                {
                  attempting = (uu___170_19356.attempting);
                  wl_deferred = (uu___170_19356.wl_deferred);
                  ctr = (uu___170_19356.ctr);
                  defer_ok = false;
                  smt_ok = (uu___170_19356.smt_ok);
                  tcenv = (uu___170_19356.tcenv);
                  wl_implicits = (uu___170_19356.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____19374  ->
                      match uu____19374 with
                      | (lb,v1) ->
                          let uu____19381 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____19381 with
                           | USolved wl1 -> ()
                           | uu____19383 -> fail1 lb v1)))
               in
            let rec check_ineq uu____19393 =
              match uu____19393 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____19402) -> true
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
                      uu____19425,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____19427,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____19438) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____19445,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____19453 -> false)
               in
            let uu____19458 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____19473  ->
                      match uu____19473 with
                      | (u,v1) ->
                          let uu____19480 = check_ineq (u, v1)  in
                          if uu____19480
                          then true
                          else
                            ((let uu____19483 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____19483
                              then
                                let uu____19484 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____19485 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____19484
                                  uu____19485
                              else ());
                             false)))
               in
            if uu____19458
            then ()
            else
              ((let uu____19489 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____19489
                then
                  ((let uu____19491 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____19491);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____19501 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____19501))
                else ());
               (let uu____19511 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____19511))
  
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
        let fail1 uu____19578 =
          match uu____19578 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___171_19599 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___171_19599.attempting);
            wl_deferred = (uu___171_19599.wl_deferred);
            ctr = (uu___171_19599.ctr);
            defer_ok;
            smt_ok = (uu___171_19599.smt_ok);
            tcenv = (uu___171_19599.tcenv);
            wl_implicits = (uu___171_19599.wl_implicits)
          }  in
        (let uu____19601 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____19601
         then
           let uu____19602 = FStar_Util.string_of_bool defer_ok  in
           let uu____19603 = wl_to_string wl  in
           let uu____19604 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____19602 uu____19603 uu____19604
         else ());
        (let g1 =
           let uu____19617 = solve_and_commit env wl fail1  in
           match uu____19617 with
           | FStar_Pervasives_Native.Some
               (uu____19624::uu____19625,uu____19626) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___172_19651 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___172_19651.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___172_19651.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____19662 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___173_19670 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___173_19670.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___173_19670.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___173_19670.FStar_TypeChecker_Env.implicits)
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
    let uu____19718 = FStar_ST.op_Bang last_proof_ns  in
    match uu____19718 with
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
            let uu___174_19841 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___174_19841.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___174_19841.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___174_19841.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____19842 =
            let uu____19843 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____19843  in
          if uu____19842
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____19851 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____19852 =
                       let uu____19853 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____19853
                        in
                     FStar_Errors.diag uu____19851 uu____19852)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____19857 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____19858 =
                        let uu____19859 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____19859
                         in
                      FStar_Errors.diag uu____19857 uu____19858)
                   else ();
                   (let uu____19862 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____19862 "discharge_guard'"
                      env vc1);
                   (let uu____19863 = check_trivial vc1  in
                    match uu____19863 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____19870 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____19871 =
                                let uu____19872 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____19872
                                 in
                              FStar_Errors.diag uu____19870 uu____19871)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____19877 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____19878 =
                                let uu____19879 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____19879
                                 in
                              FStar_Errors.diag uu____19877 uu____19878)
                           else ();
                           (let vcs =
                              let uu____19890 = FStar_Options.use_tactics ()
                                 in
                              if uu____19890
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____19909  ->
                                     (let uu____19911 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____19911);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____19913 =
                                   let uu____19920 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____19920)  in
                                 [uu____19913])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____19954  ->
                                    match uu____19954 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____19965 = check_trivial goal1
                                           in
                                        (match uu____19965 with
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
                                                (let uu____19973 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____19974 =
                                                   let uu____19975 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____19976 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____19975 uu____19976
                                                    in
                                                 FStar_Errors.diag
                                                   uu____19973 uu____19974)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____19979 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____19980 =
                                                   let uu____19981 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____19981
                                                    in
                                                 FStar_Errors.diag
                                                   uu____19979 uu____19980)
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
      let uu____19995 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____19995 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____20002 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____20002
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____20013 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____20013 with
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
            let uu____20046 = FStar_Syntax_Util.head_and_args u  in
            match uu____20046 with
            | (hd1,uu____20060) ->
                let uu____20077 =
                  let uu____20078 = FStar_Syntax_Subst.compress u  in
                  uu____20078.FStar_Syntax_Syntax.n  in
                (match uu____20077 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____20081 -> true
                 | uu____20082 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____20102 = acc  in
            match uu____20102 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____20164 = hd1  in
                     (match uu____20164 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____20181 = unresolved tm  in
                             if uu____20181
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___175_20194 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___175_20194.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___175_20194.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___175_20194.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___175_20194.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___175_20194.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___175_20194.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___175_20194.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___175_20194.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___175_20194.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___175_20194.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___175_20194.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___175_20194.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___175_20194.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___175_20194.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___175_20194.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___175_20194.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___175_20194.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___175_20194.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___175_20194.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___175_20194.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___175_20194.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___175_20194.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___175_20194.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___175_20194.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___175_20194.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___175_20194.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___175_20194.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___175_20194.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___175_20194.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___175_20194.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___175_20194.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___175_20194.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___175_20194.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___175_20194.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___175_20194.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___175_20194.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___175_20194.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___176_20197 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___176_20197.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___176_20197.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___176_20197.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___176_20197.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___176_20197.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___176_20197.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___176_20197.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___176_20197.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___176_20197.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___176_20197.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___176_20197.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___176_20197.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___176_20197.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___176_20197.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___176_20197.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___176_20197.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___176_20197.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___176_20197.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___176_20197.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___176_20197.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___176_20197.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___176_20197.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___176_20197.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___176_20197.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___176_20197.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___176_20197.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___176_20197.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___176_20197.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___176_20197.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___176_20197.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___176_20197.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___176_20197.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___176_20197.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___176_20197.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___176_20197.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___176_20197.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___176_20197.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____20200 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "RelCheck")
                                    in
                                 if uu____20200
                                 then
                                   let uu____20201 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____20202 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____20203 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____20204 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____20201 uu____20202 uu____20203
                                     reason uu____20204
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e ->
                                       ((let uu____20215 =
                                           let uu____20224 =
                                             let uu____20231 =
                                               let uu____20232 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____20233 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____20232 uu____20233
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____20231, r)
                                              in
                                           [uu____20224]  in
                                         FStar_Errors.add_errors uu____20215);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___179_20247 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___179_20247.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___179_20247.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___179_20247.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____20250 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____20257  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____20250 with
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
          let uu___180_20269 = g  in
          let uu____20270 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___180_20269.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___180_20269.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___180_20269.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____20270
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
        let uu____20324 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____20324 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____20335 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____20335
      | (reason,e,ctx_u,r,should_check)::uu____20341 ->
          let uu____20364 =
            let uu____20369 =
              let uu____20370 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____20371 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____20372 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____20370 uu____20371 reason uu____20372
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____20369)
             in
          FStar_Errors.raise_error uu____20364 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___181_20383 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___181_20383.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___181_20383.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___181_20383.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____20398 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____20398 with
      | FStar_Pervasives_Native.Some uu____20404 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____20420 = try_teq false env t1 t2  in
        match uu____20420 with
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
        (let uu____20454 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____20454
         then
           let uu____20455 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____20456 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____20455
             uu____20456
         else ());
        (let uu____20458 =
           let uu____20465 = empty_worklist env  in
           new_t_prob uu____20465 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____20458 with
         | (prob,x,wl) ->
             let g =
               let uu____20478 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____20498  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____20478  in
             ((let uu____20528 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____20528
               then
                 let uu____20529 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____20530 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____20531 =
                   let uu____20532 = FStar_Util.must g  in
                   guard_to_string env uu____20532  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____20529 uu____20530 uu____20531
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
        let uu____20566 = check_subtyping env t1 t2  in
        match uu____20566 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____20585 =
              let uu____20586 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____20586 g  in
            FStar_Pervasives_Native.Some uu____20585
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____20604 = check_subtyping env t1 t2  in
        match uu____20604 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____20623 =
              let uu____20624 =
                let uu____20625 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____20625]  in
              close_guard env uu____20624 g  in
            FStar_Pervasives_Native.Some uu____20623
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____20654 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____20654
         then
           let uu____20655 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____20656 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____20655
             uu____20656
         else ());
        (let uu____20658 =
           let uu____20665 = empty_worklist env  in
           new_t_prob uu____20665 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____20658 with
         | (prob,x,wl) ->
             let g =
               let uu____20672 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____20692  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____20672  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____20723 =
                      let uu____20724 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____20724]  in
                    close_guard env uu____20723 g1  in
                  discharge_guard_nosmt env g2))
  