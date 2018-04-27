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
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool,Prims.string
                                                            FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____4368 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4368 FStar_Util.set_elements  in
      let occurs_ok =
        let uu____4376 =
          FStar_All.pipe_right uvars1
            (FStar_Util.for_some
               (fun uv  ->
                  FStar_Syntax_Unionfind.equiv
                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                    uk.FStar_Syntax_Syntax.ctx_uvar_head))
           in
        Prims.op_Negation uu____4376  in
      let msg =
        if occurs_ok
        then FStar_Pervasives_Native.None
        else
          (let uu____4387 =
             let uu____4388 =
               FStar_Syntax_Print.uvar_to_string
                 uk.FStar_Syntax_Syntax.ctx_uvar_head
                in
             let uu____4389 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
               uu____4388 uu____4389
              in
           FStar_Pervasives_Native.Some uu____4387)
         in
      (uvars1, occurs_ok, msg)
  
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
            let uu____4478 = maximal_prefix bs_tail bs'_tail  in
            (match uu____4478 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____4522 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____4570  ->
             match uu____4570 with
             | (x,uu____4580) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____4593 = FStar_List.last bs  in
      match uu____4593 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____4611) ->
          let uu____4616 =
            FStar_Util.prefix_until
              (fun uu___106_4631  ->
                 match uu___106_4631 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____4633 -> false) g
             in
          (match uu____4616 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____4646,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____4682 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____4682 with
        | (pfx,uu____4692) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____4704 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____4704 with
             | (uu____4711,src',wl1) ->
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
      let uu____4791 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____4845  ->
                fun uu____4846  ->
                  match (uu____4845, uu____4846) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4927 =
                        let uu____4928 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____4928  in
                      if uu____4927
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____4953 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____4953
                         then
                           let uu____4966 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____4966)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____4791 with | (isect,uu____5003) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5032 'Auu____5033 .
    (FStar_Syntax_Syntax.bv,'Auu____5032) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5033) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5090  ->
              fun uu____5091  ->
                match (uu____5090, uu____5091) with
                | ((a,uu____5109),(b,uu____5111)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5126 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5126) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5156  ->
           match uu____5156 with
           | (y,uu____5162) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5173 'Auu____5174 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5173) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5174)
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
                   let uu____5283 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5283
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____5291 =
                        let uu____5294 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____5294 :: seen  in
                      aux uu____5291 args2)
               | uu____5295 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____5308 .
    ('Auu____5308,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____5319  ->
    match uu____5319 with
    | (uu____5326,c,args) ->
        let uu____5329 = print_ctx_uvar c  in
        let uu____5330 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____5329 uu____5330
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5336 =
      let uu____5337 = FStar_Syntax_Subst.compress t  in
      uu____5337.FStar_Syntax_Syntax.n  in
    match uu____5336 with
    | FStar_Syntax_Syntax.Tm_uvar uu____5340 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____5341;
           FStar_Syntax_Syntax.pos = uu____5342;
           FStar_Syntax_Syntax.vars = uu____5343;_},uu____5344)
        -> true
    | uu____5365 -> false
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> flex_t) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar uv -> (t, uv, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uv;
           FStar_Syntax_Syntax.pos = uu____5383;
           FStar_Syntax_Syntax.vars = uu____5384;_},args)
        -> (t, uv, args)
    | uu____5406 -> failwith "Not a flex-uvar"
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5434 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5471 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5477 -> false
  
let string_of_option :
  'Auu____5484 .
    ('Auu____5484 -> Prims.string) ->
      'Auu____5484 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___107_5499  ->
      match uu___107_5499 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5505 = f x  in Prims.strcat "Some " uu____5505
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___108_5510  ->
    match uu___108_5510 with
    | MisMatch (d1,d2) ->
        let uu____5521 =
          let uu____5522 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5523 =
            let uu____5524 =
              let uu____5525 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5525 ")"  in
            Prims.strcat ") (" uu____5524  in
          Prims.strcat uu____5522 uu____5523  in
        Prims.strcat "MisMatch (" uu____5521
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___109_5530  ->
    match uu___109_5530 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5545 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5575 = m2 ()  in
          (match uu____5575 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5590 -> HeadMatch)
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5603 ->
          let uu____5604 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5604 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5615 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5638 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5647 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5675 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5675
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5676 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5677 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5678 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5679 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5692 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5716) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5722,uu____5723) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5765) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5786;
             FStar_Syntax_Syntax.index = uu____5787;
             FStar_Syntax_Syntax.sort = t2;_},uu____5789)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5796 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5797 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5798 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5811 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5818 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5836 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5836
  
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
            let uu____5863 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5863
            then FullMatch
            else
              (let uu____5865 =
                 let uu____5874 =
                   let uu____5877 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5877  in
                 let uu____5878 =
                   let uu____5881 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5881  in
                 (uu____5874, uu____5878)  in
               MisMatch uu____5865)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5887),FStar_Syntax_Syntax.Tm_uinst (g,uu____5889)) ->
            let uu____5898 = head_matches env f g  in
            FStar_All.pipe_right uu____5898 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5901 = FStar_Const.eq_const c d  in
            if uu____5901
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar uv,FStar_Syntax_Syntax.Tm_uvar uv') ->
            let uu____5909 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____5909
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5916),FStar_Syntax_Syntax.Tm_refine (y,uu____5918)) ->
            let uu____5927 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5927 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5929),uu____5930) ->
            let uu____5935 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5935 head_match
        | (uu____5936,FStar_Syntax_Syntax.Tm_refine (x,uu____5938)) ->
            let uu____5943 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5943 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5944,FStar_Syntax_Syntax.Tm_type
           uu____5945) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5946,FStar_Syntax_Syntax.Tm_arrow uu____5947) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____5973),FStar_Syntax_Syntax.Tm_app (head',uu____5975))
            ->
            let uu____6016 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6016 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6018),uu____6019) ->
            let uu____6040 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6040 head_match
        | (uu____6041,FStar_Syntax_Syntax.Tm_app (head1,uu____6043)) ->
            let uu____6064 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6064 head_match
        | uu____6065 ->
            let uu____6070 =
              let uu____6079 = delta_depth_of_term env t11  in
              let uu____6082 = delta_depth_of_term env t21  in
              (uu____6079, uu____6082)  in
            MisMatch uu____6070
  
let head_matches_delta :
  'Auu____6099 .
    FStar_TypeChecker_Env.env ->
      'Auu____6099 ->
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
            let uu____6138 = FStar_Syntax_Util.head_and_args t  in
            match uu____6138 with
            | (head1,uu____6154) ->
                let uu____6171 =
                  let uu____6172 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6172.FStar_Syntax_Syntax.n  in
                (match uu____6171 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6178 =
                       let uu____6179 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6179 FStar_Option.isSome
                        in
                     if uu____6178
                     then
                       let uu____6198 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6198
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6202 -> FStar_Pervasives_Native.None)
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
                 (FStar_Syntax_Syntax.Delta_equational ),uu____6323)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6341 =
                     let uu____6350 = maybe_inline t11  in
                     let uu____6353 = maybe_inline t21  in
                     (uu____6350, uu____6353)  in
                   match uu____6341 with
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
                (uu____6390,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6408 =
                     let uu____6417 = maybe_inline t11  in
                     let uu____6420 = maybe_inline t21  in
                     (uu____6417, uu____6420)  in
                   match uu____6408 with
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
                let uu____6463 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6463 with
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
                let uu____6486 =
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
                (match uu____6486 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6510 -> fail1 r
            | uu____6519 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6532 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6532
           then
             let uu____6533 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6534 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6535 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6533
               uu____6534 uu____6535
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6553 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6553 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___110_6566  ->
    match uu___110_6566 with
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
      let uu___135_6593 = p  in
      let uu____6596 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____6597 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___135_6593.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____6596;
        FStar_TypeChecker_Common.relation =
          (uu___135_6593.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____6597;
        FStar_TypeChecker_Common.element =
          (uu___135_6593.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___135_6593.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___135_6593.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___135_6593.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___135_6593.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___135_6593.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____6611 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____6611
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____6616 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____6638 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____6638 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____6646 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____6646 with
           | (lh,lhs_args) ->
               let uu____6681 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____6681 with
                | (rh,rhs_args) ->
                    let rank =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6717,FStar_Syntax_Syntax.Tm_uvar uu____6718)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               FStar_TypeChecker_Common.Flex_flex_pattern_eq
                           | uu____6763 -> FStar_TypeChecker_Common.Flex_flex)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6784,uu____6785)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> FStar_TypeChecker_Common.Flex_rigid_eq
                      | (uu____6786,FStar_Syntax_Syntax.Tm_uvar uu____6787)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> FStar_TypeChecker_Common.Flex_rigid_eq
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6788,uu____6789)
                          -> FStar_TypeChecker_Common.Flex_rigid
                      | (uu____6790,FStar_Syntax_Syntax.Tm_uvar uu____6791)
                          -> FStar_TypeChecker_Common.Rigid_flex
                      | (uu____6792,uu____6793) ->
                          FStar_TypeChecker_Common.Rigid_rigid
                       in
                    let uu____6794 =
                      FStar_All.pipe_right
                        (let uu___136_6798 = tp  in
                         {
                           FStar_TypeChecker_Common.pid =
                             (uu___136_6798.FStar_TypeChecker_Common.pid);
                           FStar_TypeChecker_Common.lhs =
                             (uu___136_6798.FStar_TypeChecker_Common.lhs);
                           FStar_TypeChecker_Common.relation =
                             (uu___136_6798.FStar_TypeChecker_Common.relation);
                           FStar_TypeChecker_Common.rhs =
                             (uu___136_6798.FStar_TypeChecker_Common.rhs);
                           FStar_TypeChecker_Common.element =
                             (uu___136_6798.FStar_TypeChecker_Common.element);
                           FStar_TypeChecker_Common.logical_guard =
                             (uu___136_6798.FStar_TypeChecker_Common.logical_guard);
                           FStar_TypeChecker_Common.logical_guard_uvar =
                             (uu___136_6798.FStar_TypeChecker_Common.logical_guard_uvar);
                           FStar_TypeChecker_Common.reason =
                             (uu___136_6798.FStar_TypeChecker_Common.reason);
                           FStar_TypeChecker_Common.loc =
                             (uu___136_6798.FStar_TypeChecker_Common.loc);
                           FStar_TypeChecker_Common.rank =
                             (FStar_Pervasives_Native.Some rank)
                         })
                        (fun _0_24  -> FStar_TypeChecker_Common.TProb _0_24)
                       in
                    (rank, uu____6794)))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____6804 =
            FStar_All.pipe_right
              (let uu___137_6808 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___137_6808.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___137_6808.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___137_6808.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___137_6808.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___137_6808.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___137_6808.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___137_6808.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___137_6808.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___137_6808.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____6804)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____6869 probs =
      match uu____6869 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____6950 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____6971 = rank wl.tcenv hd1  in
               (match uu____6971 with
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
                      (let uu____7030 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7034 = FStar_Option.get min_rank  in
                            rank_leq rank1 uu____7034)
                          in
                       if uu____7030
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
          let uu____7106 = destruct_flex_t t  in
          match uu____7106 with
          | (uu____7107,u,uu____7109) ->
              FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
                (FStar_Util.for_some
                   (fun uu____7123  ->
                      match uu____7123 with
                      | (y,uu____7129) ->
                          FStar_All.pipe_right bs
                            (FStar_Util.for_some
                               (fun uu____7143  ->
                                  match uu____7143 with
                                  | (x,uu____7149) ->
                                      FStar_Syntax_Syntax.bv_eq x y))))
           in
        let uu____7150 = rank tcenv p  in
        match uu____7150 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____7157 -> true
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
    match projectee with | UDeferred _0 -> true | uu____7184 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____7198 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____7212 -> false
  
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
                        let uu____7264 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____7264 with
                        | (k,uu____7270) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____7280 -> false)))
            | uu____7281 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____7333 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____7339 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____7339 = (Prims.parse_int "0")))
                           in
                        if uu____7333 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____7355 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____7361 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____7361 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____7355)
               in
            let uu____7362 = filter1 u12  in
            let uu____7365 = filter1 u22  in (uu____7362, uu____7365)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____7394 = filter_out_common_univs us1 us2  in
                (match uu____7394 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____7453 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____7453 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____7456 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____7466 =
                          let uu____7467 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____7468 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____7467
                            uu____7468
                           in
                        UFailed uu____7466))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7492 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7492 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7518 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7518 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____7521 ->
                let uu____7526 =
                  let uu____7527 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____7528 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____7527
                    uu____7528 msg
                   in
                UFailed uu____7526
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____7529,uu____7530) ->
              let uu____7531 =
                let uu____7532 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7533 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7532 uu____7533
                 in
              failwith uu____7531
          | (FStar_Syntax_Syntax.U_unknown ,uu____7534) ->
              let uu____7535 =
                let uu____7536 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7537 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7536 uu____7537
                 in
              failwith uu____7535
          | (uu____7538,FStar_Syntax_Syntax.U_bvar uu____7539) ->
              let uu____7540 =
                let uu____7541 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7542 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7541 uu____7542
                 in
              failwith uu____7540
          | (uu____7543,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____7544 =
                let uu____7545 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7546 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7545 uu____7546
                 in
              failwith uu____7544
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____7570 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____7570
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____7584 = occurs_univ v1 u3  in
              if uu____7584
              then
                let uu____7585 =
                  let uu____7586 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7587 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7586 uu____7587
                   in
                try_umax_components u11 u21 uu____7585
              else
                (let uu____7589 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7589)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____7601 = occurs_univ v1 u3  in
              if uu____7601
              then
                let uu____7602 =
                  let uu____7603 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7604 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7603 uu____7604
                   in
                try_umax_components u11 u21 uu____7602
              else
                (let uu____7606 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7606)
          | (FStar_Syntax_Syntax.U_max uu____7607,uu____7608) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7614 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7614
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____7616,FStar_Syntax_Syntax.U_max uu____7617) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7623 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7623
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____7625,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____7626,FStar_Syntax_Syntax.U_name
             uu____7627) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____7628) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____7629) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7630,FStar_Syntax_Syntax.U_succ
             uu____7631) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7632,FStar_Syntax_Syntax.U_zero
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
      let uu____7732 = bc1  in
      match uu____7732 with
      | (bs1,mk_cod1) ->
          let uu____7776 = bc2  in
          (match uu____7776 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____7887 = aux xs ys  in
                     (match uu____7887 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____7970 =
                       let uu____7977 = mk_cod1 xs  in ([], uu____7977)  in
                     let uu____7980 =
                       let uu____7987 = mk_cod2 ys  in ([], uu____7987)  in
                     (uu____7970, uu____7980)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____8010 'Auu____8011 'Auu____8012 .
    ('Auu____8010,'Auu____8011,'Auu____8012 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___111_8025  ->
    match uu___111_8025 with
    | (uu____8034,uu____8035,[]) -> true
    | uu____8038 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8069 = f  in
      match uu____8069 with
      | (uu____8076,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8077;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8078;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8081;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8082;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8083;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____8135  ->
                 match uu____8135 with
                 | (y,uu____8141) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                FStar_Pervasives_Native.Some
                  ((FStar_List.rev pat_binders), t_res)
            | (uu____8247,[]) ->
                FStar_Pervasives_Native.Some
                  ((FStar_List.rev pat_binders), t_res)
            | ((formal,uu____8279)::formals1,(a,uu____8282)::args2) ->
                let uu____8316 =
                  let uu____8317 = FStar_Syntax_Subst.compress a  in
                  uu____8317.FStar_Syntax_Syntax.n  in
                (match uu____8316 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____8329 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____8329
                     then
                       let uu____8338 =
                         let uu____8341 =
                           FStar_Syntax_Syntax.mk_binder formal  in
                         uu____8341 :: pat_binders  in
                       aux uu____8338 formals1 t_res args2
                     else
                       (let x1 =
                          let uu___138_8344 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_8344.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_8344.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____8348 =
                            let uu____8349 =
                              let uu____8356 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____8356)  in
                            FStar_Syntax_Syntax.NT uu____8349  in
                          [uu____8348]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        let uu____8363 =
                          let uu____8366 =
                            FStar_Syntax_Syntax.mk_binder
                              (let uu___139_8369 = x1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___139_8369.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___139_8369.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort =
                                   (formal.FStar_Syntax_Syntax.sort)
                               })
                             in
                          uu____8366 :: pat_binders  in
                        aux uu____8363 formals2 t_res1 args2)
                 | uu____8370 ->
                     let uu____8371 =
                       let uu____8374 = FStar_Syntax_Syntax.mk_binder formal
                          in
                       uu____8374 :: pat_binders  in
                     aux uu____8371 formals1 t_res args2)
            | ([],args2) ->
                let uu____8398 =
                  let uu____8411 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____8411  in
                (match uu____8398 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____8456 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____8483 ->
               let uu____8484 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____8484 with
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
            let uu____8595 =
              new_problem wl1 env t1 FStar_TypeChecker_Common.EQ t2
                FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                "join/meet refinements"
               in
            match uu____8595 with
            | (p,wl2) -> ((FStar_TypeChecker_Common.TProb p), wl2)  in
          let pairwise t1 t2 wl1 =
            let uu____8640 = head_matches_delta env () t1 t2  in
            match uu____8640 with
            | (mr,ts1) ->
                (match mr with
                 | MisMatch uu____8681 ->
                     let uu____8690 = eq_prob t1 t2 wl1  in
                     (match uu____8690 with | (p,wl2) -> (t1, [p], wl2))
                 | FullMatch  ->
                     (match ts1 with
                      | FStar_Pervasives_Native.None  -> (t1, [], wl1)
                      | FStar_Pervasives_Native.Some (t11,t21) ->
                          (t11, [], wl1))
                 | HeadMatch  ->
                     let uu____8729 =
                       match ts1 with
                       | FStar_Pervasives_Native.Some (t11,t21) ->
                           let uu____8744 = FStar_Syntax_Subst.compress t11
                              in
                           let uu____8745 = FStar_Syntax_Subst.compress t21
                              in
                           (uu____8744, uu____8745)
                       | FStar_Pervasives_Native.None  ->
                           let uu____8750 = FStar_Syntax_Subst.compress t1
                              in
                           let uu____8751 = FStar_Syntax_Subst.compress t2
                              in
                           (uu____8750, uu____8751)
                        in
                     (match uu____8729 with
                      | (t11,t21) ->
                          (match (t11, t21) with
                           | ({
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_refine (x,phi1);
                                FStar_Syntax_Syntax.pos = uu____8776;
                                FStar_Syntax_Syntax.vars = uu____8777;_},
                              {
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_refine (y,phi2);
                                FStar_Syntax_Syntax.pos = uu____8780;
                                FStar_Syntax_Syntax.vars = uu____8781;_})
                               ->
                               let uu____8798 =
                                 eq_prob x.FStar_Syntax_Syntax.sort
                                   y.FStar_Syntax_Syntax.sort wl1
                                  in
                               (match uu____8798 with
                                | (p,wl2) ->
                                    let x1 = FStar_Syntax_Syntax.freshen_bv x
                                       in
                                    let subst1 =
                                      [FStar_Syntax_Syntax.DB
                                         ((Prims.parse_int "0"), x1)]
                                       in
                                    let phi11 =
                                      FStar_Syntax_Subst.subst subst1 phi1
                                       in
                                    let phi21 =
                                      FStar_Syntax_Subst.subst subst1 phi2
                                       in
                                    let uu____8819 =
                                      let uu____8822 = op phi11 phi21  in
                                      FStar_Syntax_Util.refine x1 uu____8822
                                       in
                                    (uu____8819, [p], wl2))
                           | (t,{
                                  FStar_Syntax_Syntax.n =
                                    FStar_Syntax_Syntax.Tm_refine (x,phi);
                                  FStar_Syntax_Syntax.pos = uu____8832;
                                  FStar_Syntax_Syntax.vars = uu____8833;_})
                               ->
                               let uu____8846 =
                                 eq_prob x.FStar_Syntax_Syntax.sort t wl1  in
                               (match uu____8846 with
                                | (p,wl2) ->
                                    let x1 = FStar_Syntax_Syntax.freshen_bv x
                                       in
                                    let subst1 =
                                      [FStar_Syntax_Syntax.DB
                                         ((Prims.parse_int "0"), x1)]
                                       in
                                    let phi1 =
                                      FStar_Syntax_Subst.subst subst1 phi  in
                                    let uu____8866 =
                                      let uu____8869 =
                                        op FStar_Syntax_Util.t_true phi1  in
                                      FStar_Syntax_Util.refine x1 uu____8869
                                       in
                                    (uu____8866, [p], wl2))
                           | ({
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Tm_refine (x,phi);
                                FStar_Syntax_Syntax.pos = uu____8878;
                                FStar_Syntax_Syntax.vars = uu____8879;_},t)
                               ->
                               let uu____8893 =
                                 eq_prob x.FStar_Syntax_Syntax.sort t wl1  in
                               (match uu____8893 with
                                | (p,wl2) ->
                                    let x1 = FStar_Syntax_Syntax.freshen_bv x
                                       in
                                    let subst1 =
                                      [FStar_Syntax_Syntax.DB
                                         ((Prims.parse_int "0"), x1)]
                                       in
                                    let phi1 =
                                      FStar_Syntax_Subst.subst subst1 phi  in
                                    let uu____8913 =
                                      let uu____8916 =
                                        op FStar_Syntax_Util.t_true phi1  in
                                      FStar_Syntax_Util.refine x1 uu____8916
                                       in
                                    (uu____8913, [p], wl2))
                           | uu____8923 ->
                               let uu____8932 = eq_prob t11 t21 wl1  in
                               (match uu____8932 with
                                | (p,wl2) -> (t11, [p], wl2)))))
             in
          let rec aux uu____8978 ts1 =
            match uu____8978 with
            | (out,probs,wl1) ->
                (match ts1 with
                 | [] -> (out, probs, wl1)
                 | t::ts2 ->
                     let uu____9029 = pairwise out t wl1  in
                     (match uu____9029 with
                      | (out1,probs',wl2) ->
                          aux (out1, (FStar_List.append probs probs'), wl2)
                            ts2))
             in
          let uu____9055 =
            let uu____9064 = FStar_List.hd ts  in (uu____9064, [], wl)  in
          let uu____9067 = FStar_List.tl ts  in aux uu____9055 uu____9067
  
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
      (let uu____9357 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9357
       then
         let uu____9358 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9358
       else ());
      (let uu____9360 = next_prob probs  in
       match uu____9360 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___140_9387 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___140_9387.wl_deferred);
               ctr = (uu___140_9387.ctr);
               defer_ok = (uu___140_9387.defer_ok);
               smt_ok = (uu___140_9387.smt_ok);
               tcenv = (uu___140_9387.tcenv);
               wl_implicits = (uu___140_9387.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____9394 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____9394
                then
                  let uu____9395 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____9395
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
                          (let uu___141_9400 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___141_9400.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___141_9400.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___141_9400.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___141_9400.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___141_9400.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___141_9400.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___141_9400.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___141_9400.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___141_9400.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9422 ->
                let uu____9431 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9490  ->
                          match uu____9490 with
                          | (c,uu____9498,uu____9499) -> c < probs.ctr))
                   in
                (match uu____9431 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9540 =
                            let uu____9545 =
                              FStar_List.map
                                (fun uu____9560  ->
                                   match uu____9560 with
                                   | (uu____9571,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9545, (probs.wl_implicits))  in
                          Success uu____9540
                      | uu____9574 ->
                          let uu____9583 =
                            let uu___142_9584 = probs  in
                            let uu____9585 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9604  ->
                                      match uu____9604 with
                                      | (uu____9611,uu____9612,y) -> y))
                               in
                            {
                              attempting = uu____9585;
                              wl_deferred = rest;
                              ctr = (uu___142_9584.ctr);
                              defer_ok = (uu___142_9584.defer_ok);
                              smt_ok = (uu___142_9584.smt_ok);
                              tcenv = (uu___142_9584.tcenv);
                              wl_implicits = (uu___142_9584.wl_implicits)
                            }  in
                          solve env uu____9583))))

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
            let uu____9619 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9619 with
            | USolved wl1 ->
                let uu____9621 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9621
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
                  let uu____9673 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____9673 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9676 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9688;
                  FStar_Syntax_Syntax.vars = uu____9689;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9692;
                  FStar_Syntax_Syntax.vars = uu____9693;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9705,uu____9706) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9713,FStar_Syntax_Syntax.Tm_uinst uu____9714) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9721 -> USolved wl

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
            ((let uu____9731 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____9731
              then
                let uu____9732 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9732 msg
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
          let uu____9740 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____9740 with
          | (this_flex,this_rigid) ->
              let uu____9752 =
                let uu____9753 = FStar_Syntax_Subst.compress this_rigid  in
                uu____9753.FStar_Syntax_Syntax.n  in
              (match uu____9752 with
               | FStar_Syntax_Syntax.Tm_arrow uu____9756 ->
                   let flex = destruct_flex_t this_flex  in
                   let uu____9770 = quasi_pattern env flex  in
                   (match uu____9770 with
                    | FStar_Pervasives_Native.None  ->
                        giveup env
                          "flex-arrow subtyping, not a quasi pattern"
                          (FStar_TypeChecker_Common.TProb tp)
                    | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                        ((let uu____9788 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelCheck")
                             in
                          if uu____9788
                          then
                            let uu____9789 =
                              FStar_Util.string_of_int
                                tp.FStar_TypeChecker_Common.pid
                               in
                            FStar_Util.print1
                              "Trying to solve by imitating arrow:%s\n"
                              uu____9789
                          else ());
                         imitate_arrow (FStar_TypeChecker_Common.TProb tp)
                           env wl flex flex_bs flex_t
                           tp.FStar_TypeChecker_Common.relation this_rigid))
               | uu____9791 ->
                   ((let uu____9793 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____9793
                     then
                       let uu____9794 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____9794
                     else ());
                    (let uu____9796 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____9796 with
                     | (u,_args) ->
                         let uu____9827 =
                           let uu____9828 = FStar_Syntax_Subst.compress u  in
                           uu____9828.FStar_Syntax_Syntax.n  in
                         (match uu____9827 with
                          | FStar_Syntax_Syntax.Tm_uvar ctx_uvar ->
                              let equiv1 t =
                                let uu____9838 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____9838 with
                                | (u',uu____9852) ->
                                    let uu____9869 =
                                      let uu____9870 = whnf env u'  in
                                      uu____9870.FStar_Syntax_Syntax.n  in
                                    (match uu____9869 with
                                     | FStar_Syntax_Syntax.Tm_uvar ctx_uvar'
                                         ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____9874 -> false)
                                 in
                              let uu____9875 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___112_9898  ->
                                        match uu___112_9898 with
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
                                             | uu____9907 -> false)
                                        | uu____9910 -> false))
                                 in
                              (match uu____9875 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____9924 = whnf env this_rigid  in
                                     let uu____9925 =
                                       FStar_List.collect
                                         (fun uu___113_9931  ->
                                            match uu___113_9931 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____9937 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____9937]
                                            | uu____9939 -> []) bounds_probs
                                        in
                                     uu____9924 :: uu____9925  in
                                   let uu____9940 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____9940 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____9965 =
                                          new_problem wl1 env bound
                                            FStar_TypeChecker_Common.EQ
                                            this_flex
                                            FStar_Pervasives_Native.None
                                            tp.FStar_TypeChecker_Common.loc
                                            (if flip
                                             then "joining refinements"
                                             else "meeting refinements")
                                           in
                                        (match uu____9965 with
                                         | (eq_prob,wl2) ->
                                             ((let uu____9980 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "RelCheck")
                                                  in
                                               if uu____9980
                                               then
                                                 let wl' =
                                                   let uu___143_9982 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___143_9982.wl_deferred);
                                                     ctr =
                                                       (uu___143_9982.ctr);
                                                     defer_ok =
                                                       (uu___143_9982.defer_ok);
                                                     smt_ok =
                                                       (uu___143_9982.smt_ok);
                                                     tcenv =
                                                       (uu___143_9982.tcenv);
                                                     wl_implicits =
                                                       (uu___143_9982.wl_implicits)
                                                   }  in
                                                 let uu____9983 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____9983
                                               else ());
                                              (let uu____9985 =
                                                 solve_t env eq_prob
                                                   (let uu___144_9987 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___144_9987.wl_deferred);
                                                      ctr =
                                                        (uu___144_9987.ctr);
                                                      defer_ok =
                                                        (uu___144_9987.defer_ok);
                                                      smt_ok =
                                                        (uu___144_9987.smt_ok);
                                                      tcenv =
                                                        (uu___144_9987.tcenv);
                                                      wl_implicits =
                                                        (uu___144_9987.wl_implicits)
                                                    })
                                                  in
                                               match uu____9985 with
                                               | Success uu____9988 ->
                                                   let wl3 =
                                                     let uu___145_9994 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___145_9994.wl_deferred);
                                                       ctr =
                                                         (uu___145_9994.ctr);
                                                       defer_ok =
                                                         (uu___145_9994.defer_ok);
                                                       smt_ok =
                                                         (uu___145_9994.smt_ok);
                                                       tcenv =
                                                         (uu___145_9994.tcenv);
                                                       wl_implicits =
                                                         (uu___145_9994.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____9998 =
                                                     FStar_List.fold_left
                                                       (fun wl5  ->
                                                          fun p  ->
                                                            solve_prob' true
                                                              p
                                                              FStar_Pervasives_Native.None
                                                              [] wl5) wl4
                                                       bounds_probs
                                                      in
                                                   solve env wl4
                                               | Failed (p,msg) ->
                                                   giveup env
                                                     (Prims.strcat
                                                        "failed to solve sub-problems: "
                                                        msg)
                                                     (FStar_TypeChecker_Common.TProb
                                                        tp))))))
                          | uu____10007 when flip ->
                              let uu____10008 =
                                let uu____10009 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a flex-rigid: %s"
                                  uu____10009
                                 in
                              failwith uu____10008
                          | uu____10010 ->
                              let uu____10011 =
                                let uu____10012 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a rigid-flex: %s"
                                  uu____10012
                                 in
                              failwith uu____10011))))

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
                      (fun uu____10040  ->
                         match uu____10040 with
                         | (x,i) ->
                             let uu____10051 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____10051, i)) bs_lhs
                     in
                  let uu____10052 = lhs  in
                  match uu____10052 with
                  | (uu____10053,u_lhs,uu____10055) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____10168 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____10178 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____10178, univ)
                             in
                          match uu____10168 with
                          | (k,univ) ->
                              let uu____10191 =
                                let uu____10198 =
                                  let uu____10201 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____10201
                                   in
                                copy_uvar u_lhs uu____10198 wl2  in
                              (match uu____10191 with
                               | (uu____10214,u,wl3) ->
                                   let uu____10217 =
                                     let uu____10220 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____10220
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____10217, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____10256 =
                              let uu____10269 =
                                let uu____10278 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____10278 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____10324  ->
                                   fun uu____10325  ->
                                     match (uu____10324, uu____10325) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____10416 =
                                           let uu____10423 =
                                             let uu____10426 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____10426
                                              in
                                           copy_uvar u_lhs uu____10423 wl2
                                            in
                                         (match uu____10416 with
                                          | (uu____10455,t_a,wl3) ->
                                              let uu____10458 =
                                                let uu____10465 =
                                                  let uu____10468 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____10468
                                                   in
                                                copy_uvar u_lhs uu____10465
                                                  wl3
                                                 in
                                              (match uu____10458 with
                                               | (uu____10483,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____10269
                                ([], wl1)
                               in
                            (match uu____10256 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___146_10544 = ct  in
                                   let uu____10545 =
                                     let uu____10548 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____10548
                                      in
                                   let uu____10563 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___146_10544.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___146_10544.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____10545;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____10563;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___146_10544.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___147_10581 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___147_10581.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___147_10581.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____10584 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____10584 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____10638 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____10638 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____10655 =
                                          let uu____10660 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____10660)  in
                                        TERM uu____10655  in
                                      let uu____10661 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____10661 with
                                       | (sub_prob,wl3) ->
                                           let uu____10672 =
                                             let uu____10673 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____10673
                                              in
                                           solve env uu____10672))
                             | (x,imp)::formals2 ->
                                 let uu____10687 =
                                   let uu____10694 =
                                     let uu____10697 =
                                       let uu____10700 =
                                         let uu____10701 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____10701
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____10700
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____10697
                                      in
                                   copy_uvar u_lhs uu____10694 wl1  in
                                 (match uu____10687 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____10725 =
                                          let uu____10728 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____10728
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____10725 t_y
                                         in
                                      let uu____10729 =
                                        let uu____10732 =
                                          let uu____10735 =
                                            let uu____10736 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____10736, imp)  in
                                          [uu____10735]  in
                                        FStar_List.append bs_terms
                                          uu____10732
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____10729 formals2 wl2)
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
              (let uu____10778 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10778
               then
                 let uu____10779 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____10780 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____10779 (rel_to_string (p_rel orig)) uu____10780
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____10885 = rhs wl1 scope env1 subst1  in
                     (match uu____10885 with
                      | (rhs_prob,wl2) ->
                          ((let uu____10905 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____10905
                            then
                              let uu____10906 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____10906
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___148_10960 = hd1  in
                       let uu____10961 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___148_10960.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___148_10960.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____10961
                       }  in
                     let hd21 =
                       let uu___149_10965 = hd2  in
                       let uu____10966 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___149_10965.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___149_10965.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____10966
                       }  in
                     let uu____10969 =
                       let uu____10974 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____10974
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____10969 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____10993 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____10993
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____10997 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____10997 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____11052 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____11052
                                  in
                               ((let uu____11064 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11064
                                 then
                                   let uu____11065 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____11066 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____11065
                                     uu____11066
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____11093 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____11122 = aux wl [] env [] bs1 bs2  in
               match uu____11122 with
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
        (let uu____11173 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____11173 wl)

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
              let uu____11187 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____11187 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____11217 = lhs1  in
              match uu____11217 with
              | (uu____11220,ctx_u,uu____11222) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____11228 ->
                        let uu____11229 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____11229 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____11276 = quasi_pattern env1 lhs1  in
              match uu____11276 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____11306) ->
                  let uu____11311 = lhs1  in
                  (match uu____11311 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____11325 = occurs_check ctx_u rhs1  in
                       (match uu____11325 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____11367 =
                                let uu____11374 =
                                  let uu____11375 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____11375
                                   in
                                FStar_Util.Inl uu____11374  in
                              (uu____11367, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____11395 =
                                 let uu____11396 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____11396  in
                               if uu____11395
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____11416 =
                                    let uu____11423 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____11423  in
                                  let uu____11428 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____11416, uu____11428)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____11490  ->
                     match uu____11490 with
                     | (x,i) ->
                         let uu____11501 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____11501, i)) bs_lhs
                 in
              let uu____11502 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____11502 with
              | (rhs_hd,args) ->
                  let uu____11533 = FStar_Util.prefix args  in
                  (match uu____11533 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____11591 = lhs1  in
                       (match uu____11591 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____11595 =
                              let uu____11606 =
                                let uu____11613 =
                                  let uu____11616 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____11616
                                   in
                                copy_uvar u_lhs uu____11613 wl1  in
                              match uu____11606 with
                              | (uu____11643,t_last_arg,wl2) ->
                                  let uu____11646 =
                                    let uu____11653 =
                                      let uu____11656 =
                                        let uu____11663 =
                                          let uu____11670 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____11670]  in
                                        FStar_List.append bs_lhs uu____11663
                                         in
                                      let uu____11687 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____11656
                                        uu____11687
                                       in
                                    copy_uvar u_lhs uu____11653 wl2  in
                                  (match uu____11646 with
                                   | (uu____11700,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____11706 =
                                         let uu____11713 =
                                           let uu____11716 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____11716
                                            in
                                         copy_uvar u_lhs uu____11713 wl3  in
                                       (match uu____11706 with
                                        | (uu____11729,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____11595 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____11753 =
                                     let uu____11754 =
                                       let uu____11759 =
                                         let uu____11760 =
                                           let uu____11763 =
                                             let uu____11768 =
                                               let uu____11769 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____11769]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____11768
                                              in
                                           uu____11763
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____11760
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____11759)  in
                                     TERM uu____11754  in
                                   [uu____11753]  in
                                 let uu____11790 =
                                   let uu____11797 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____11797 with
                                   | (p1,wl3) ->
                                       let uu____11814 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____11814 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____11790 with
                                  | (sub_probs,wl3) ->
                                      let uu____11841 =
                                        let uu____11842 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____11842  in
                                      solve env1 uu____11841))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____11875 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____11875 with
                | (uu____11888,args) ->
                    (match args with | [] -> false | uu____11912 -> true)
                 in
              let is_arrow rhs2 =
                let uu____11927 =
                  let uu____11928 = FStar_Syntax_Subst.compress rhs2  in
                  uu____11928.FStar_Syntax_Syntax.n  in
                match uu____11927 with
                | FStar_Syntax_Syntax.Tm_arrow uu____11931 -> true
                | uu____11944 -> false  in
              let uu____11945 = quasi_pattern env1 lhs1  in
              match uu____11945 with
              | FStar_Pervasives_Native.None  ->
                  let uu____11956 =
                    let uu____11957 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____11957
                     in
                  giveup_or_defer env1 orig1 wl1 uu____11956
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____11964 = is_app rhs1  in
                  if uu____11964
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____11966 = is_arrow rhs1  in
                     if uu____11966
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____11968 =
                          let uu____11969 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____11969
                           in
                        giveup_or_defer env1 orig1 wl1 uu____11968))
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
                let uu____11972 = lhs  in
                (match uu____11972 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____11976 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____11976 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____11991 =
                              let uu____11994 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____11994
                               in
                            FStar_All.pipe_right uu____11991
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____12009 = occurs_check ctx_uv rhs1  in
                          (match uu____12009 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____12031 =
                                   let uu____12032 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____12032
                                    in
                                 giveup_or_defer env orig wl uu____12031
                               else
                                 (let uu____12034 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____12034
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____12039 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____12039
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____12041 =
                                         let uu____12042 =
                                           names_to_string1 fvs2  in
                                         let uu____12043 =
                                           names_to_string1 fvs1  in
                                         let uu____12044 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____12042 uu____12043
                                           uu____12044
                                          in
                                       giveup_or_defer env orig wl
                                         uu____12041)
                                    else first_order orig env wl lhs rhs1))
                      | uu____12050 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____12054 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____12054 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____12077 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____12077
                             | (FStar_Util.Inl msg,uu____12079) ->
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
                  (let uu____12108 =
                     let uu____12125 = quasi_pattern env lhs  in
                     let uu____12132 = quasi_pattern env rhs  in
                     (uu____12125, uu____12132)  in
                   match uu____12108 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____12175 = lhs  in
                       (match uu____12175 with
                        | ({ FStar_Syntax_Syntax.n = uu____12176;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____12178;_},u_lhs,uu____12180)
                            ->
                            let uu____12183 = rhs  in
                            (match uu____12183 with
                             | (uu____12184,u_rhs,uu____12186) ->
                                 let uu____12187 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____12187
                                 then
                                   let uu____12188 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____12188
                                 else
                                   (let uu____12190 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____12190 with
                                    | (sub_prob,wl1) ->
                                        let uu____12201 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____12201 with
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
                                             let uu____12229 =
                                               let uu____12236 =
                                                 let uu____12239 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____12239
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi: lhs="
                                                    (Prims.strcat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.strcat ", rhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))
                                                 wl1 range gamma_w ctx_w
                                                 uu____12236
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____12229 with
                                              | (uu____12242,w,wl2) ->
                                                  let w_app =
                                                    let uu____12248 =
                                                      let uu____12253 =
                                                        FStar_List.map
                                                          (fun uu____12262 
                                                             ->
                                                             match uu____12262
                                                             with
                                                             | (z,uu____12268)
                                                                 ->
                                                                 let uu____12269
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____12269)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____12253
                                                       in
                                                    uu____12248
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____12273 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "RelCheck")
                                                       in
                                                    if uu____12273
                                                    then
                                                      let uu____12274 =
                                                        flex_t_to_string lhs
                                                         in
                                                      let uu____12275 =
                                                        flex_t_to_string rhs
                                                         in
                                                      let uu____12276 =
                                                        let uu____12277 =
                                                          destruct_flex_t w
                                                           in
                                                        flex_t_to_string
                                                          uu____12277
                                                         in
                                                      FStar_Util.print3
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s"
                                                        uu____12274
                                                        uu____12275
                                                        uu____12276
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____12289 =
                                                          let uu____12294 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____12294)
                                                           in
                                                        TERM uu____12289  in
                                                      let uu____12295 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____12295
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____12300 =
                                                             let uu____12305
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
                                                               uu____12305)
                                                              in
                                                           TERM uu____12300
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____12306 =
                                                      let uu____12307 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____12307
                                                       in
                                                    solve env uu____12306)))))))
                   | uu____12308 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____12376 = head_matches_delta env1 wl1 t1 t2  in
           match uu____12376 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____12407,uu____12408) ->
                    let rec may_relate head3 =
                      let uu____12435 =
                        let uu____12436 = FStar_Syntax_Subst.compress head3
                           in
                        uu____12436.FStar_Syntax_Syntax.n  in
                      match uu____12435 with
                      | FStar_Syntax_Syntax.Tm_name uu____12439 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____12440 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12463;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational ;
                            FStar_Syntax_Syntax.fv_qual = uu____12464;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____12467;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____12468;
                            FStar_Syntax_Syntax.fv_qual = uu____12469;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____12473,uu____12474) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____12516) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____12522) ->
                          may_relate t
                      | uu____12527 -> false  in
                    let uu____12528 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____12528
                    then
                      let uu____12529 =
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
                                 let uu____12561 =
                                   let uu____12562 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____12562 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____12561
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____12567 = has_type_guard t1 t2  in
                             (uu____12567, wl1)
                           else
                             (let uu____12573 = has_type_guard t2 t1  in
                              (uu____12573, wl1)))
                         in
                      (match uu____12529 with
                       | (guard,wl2) ->
                           let uu____12580 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____12580)
                    else
                      (let uu____12582 =
                         let uu____12583 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____12584 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____12583 uu____12584
                          in
                       giveup env1 uu____12582 orig)
                | (uu____12585,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___150_12599 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___150_12599.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___150_12599.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___150_12599.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___150_12599.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___150_12599.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___150_12599.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___150_12599.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___150_12599.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____12600,FStar_Pervasives_Native.None ) ->
                    ((let uu____12612 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12612
                      then
                        let uu____12613 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____12614 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____12615 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____12616 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____12613
                          uu____12614 uu____12615 uu____12616
                      else ());
                     (let uu____12618 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____12618 with
                      | (head11,args1) ->
                          let uu____12649 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____12649 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____12697 =
                                   let uu____12698 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____12699 = args_to_string args1  in
                                   let uu____12700 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____12701 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____12698 uu____12699 uu____12700
                                     uu____12701
                                    in
                                 giveup env1 uu____12697 orig
                               else
                                 (let uu____12703 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____12710 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____12710 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____12703
                                  then
                                    let uu____12711 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____12711 with
                                    | USolved wl2 ->
                                        let uu____12713 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____12713
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____12717 =
                                       base_and_refinement env1 t1  in
                                     match uu____12717 with
                                     | (base1,refinement1) ->
                                         let uu____12742 =
                                           base_and_refinement env1 t2  in
                                         (match uu____12742 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____12799 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____12799 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____12803 =
                                                          FStar_List.fold_right2
                                                            (fun uu____12836 
                                                               ->
                                                               fun
                                                                 uu____12837 
                                                                 ->
                                                                 fun
                                                                   uu____12838
                                                                    ->
                                                                   match 
                                                                    (uu____12836,
                                                                    uu____12837,
                                                                    uu____12838)
                                                                   with
                                                                   | 
                                                                   ((a,uu____12874),
                                                                    (a',uu____12876),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____12897
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____12897
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
                                                        (match uu____12803
                                                         with
                                                         | (subprobs,wl3) ->
                                                             let formula =
                                                               let uu____12927
                                                                 =
                                                                 FStar_List.map
                                                                   (fun p  ->
                                                                    p_guard p)
                                                                   subprobs
                                                                  in
                                                               FStar_Syntax_Util.mk_conj_l
                                                                 uu____12927
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
                                               | uu____12935 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___151_12975 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___151_12975.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____12978 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____12978
          then
            let uu____12979 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____12979
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____12984 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "RelCheck")
                 in
              if uu____12984
              then
                let uu____12985 = FStar_Syntax_Print.tag_of_term t1  in
                let uu____12986 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____12987 = prob_to_string env orig  in
                FStar_Util.print3 "Attempting (%s - %s)\n%s\n" uu____12985
                  uu____12986 uu____12987
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____12990,uu____12991) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____13016,FStar_Syntax_Syntax.Tm_delayed uu____13017) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____13042,uu____13043) ->
                  let uu____13070 =
                    let uu___152_13071 = problem  in
                    let uu____13072 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___152_13071.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____13072;
                      FStar_TypeChecker_Common.relation =
                        (uu___152_13071.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___152_13071.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___152_13071.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___152_13071.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___152_13071.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___152_13071.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___152_13071.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___152_13071.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13070 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____13073,uu____13074) ->
                  let uu____13081 =
                    let uu___153_13082 = problem  in
                    let uu____13083 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___153_13082.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____13083;
                      FStar_TypeChecker_Common.relation =
                        (uu___153_13082.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___153_13082.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___153_13082.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___153_13082.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___153_13082.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___153_13082.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___153_13082.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___153_13082.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13081 wl
              | (uu____13084,FStar_Syntax_Syntax.Tm_ascribed uu____13085) ->
                  let uu____13112 =
                    let uu___154_13113 = problem  in
                    let uu____13114 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___154_13113.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___154_13113.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___154_13113.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____13114;
                      FStar_TypeChecker_Common.element =
                        (uu___154_13113.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___154_13113.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___154_13113.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___154_13113.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___154_13113.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___154_13113.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13112 wl
              | (uu____13115,FStar_Syntax_Syntax.Tm_meta uu____13116) ->
                  let uu____13123 =
                    let uu___155_13124 = problem  in
                    let uu____13125 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___155_13124.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___155_13124.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___155_13124.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____13125;
                      FStar_TypeChecker_Common.element =
                        (uu___155_13124.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___155_13124.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___155_13124.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___155_13124.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___155_13124.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___155_13124.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13123 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____13127),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____13129)) ->
                  let uu____13138 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____13138
              | (FStar_Syntax_Syntax.Tm_bvar uu____13139,uu____13140) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____13141,FStar_Syntax_Syntax.Tm_bvar uu____13142) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___114_13201 =
                    match uu___114_13201 with
                    | [] -> c
                    | bs ->
                        let uu____13223 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____13223
                     in
                  let uu____13232 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____13232 with
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
                                    let uu____13355 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____13355
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
                  let mk_t t l uu___115_13430 =
                    match uu___115_13430 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____13464 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____13464 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____13583 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____13584 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____13583
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____13584 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____13585,uu____13586) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____13613 -> true
                    | uu____13630 -> false  in
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
                      (let uu____13673 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___156_13681 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___156_13681.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___156_13681.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___156_13681.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___156_13681.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___156_13681.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___156_13681.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___156_13681.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___156_13681.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___156_13681.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___156_13681.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___156_13681.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___156_13681.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___156_13681.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___156_13681.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___156_13681.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___156_13681.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___156_13681.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___156_13681.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___156_13681.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___156_13681.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___156_13681.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___156_13681.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___156_13681.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___156_13681.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___156_13681.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___156_13681.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___156_13681.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___156_13681.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___156_13681.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___156_13681.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___156_13681.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___156_13681.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___156_13681.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___156_13681.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___156_13681.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____13673 with
                       | (uu____13684,ty,uu____13686) ->
                           let uu____13687 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____13687)
                     in
                  let uu____13688 =
                    let uu____13701 = maybe_eta t1  in
                    let uu____13706 = maybe_eta t2  in
                    (uu____13701, uu____13706)  in
                  (match uu____13688 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___157_13730 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___157_13730.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___157_13730.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___157_13730.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___157_13730.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___157_13730.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___157_13730.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___157_13730.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___157_13730.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____13741 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____13741
                       then
                         let uu____13742 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____13742 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___158_13751 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_13751.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___158_13751.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_13751.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_13751.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___158_13751.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_13751.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_13751.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_13751.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____13763 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____13763
                       then
                         let uu____13764 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____13764 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___158_13773 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_13773.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___158_13773.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_13773.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_13773.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___158_13773.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_13773.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_13773.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_13773.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____13775 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____13788,FStar_Syntax_Syntax.Tm_abs uu____13789) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____13816 -> true
                    | uu____13833 -> false  in
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
                      (let uu____13876 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___156_13884 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___156_13884.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___156_13884.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___156_13884.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___156_13884.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___156_13884.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___156_13884.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___156_13884.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___156_13884.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___156_13884.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___156_13884.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___156_13884.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___156_13884.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___156_13884.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___156_13884.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___156_13884.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___156_13884.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___156_13884.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___156_13884.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___156_13884.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___156_13884.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___156_13884.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___156_13884.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___156_13884.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___156_13884.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___156_13884.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___156_13884.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___156_13884.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___156_13884.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___156_13884.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___156_13884.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___156_13884.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___156_13884.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___156_13884.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___156_13884.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___156_13884.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____13876 with
                       | (uu____13887,ty,uu____13889) ->
                           let uu____13890 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____13890)
                     in
                  let uu____13891 =
                    let uu____13904 = maybe_eta t1  in
                    let uu____13909 = maybe_eta t2  in
                    (uu____13904, uu____13909)  in
                  (match uu____13891 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___157_13933 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___157_13933.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___157_13933.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___157_13933.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___157_13933.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___157_13933.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___157_13933.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___157_13933.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___157_13933.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____13944 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____13944
                       then
                         let uu____13945 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____13945 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___158_13954 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_13954.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___158_13954.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_13954.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_13954.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___158_13954.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_13954.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_13954.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_13954.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____13966 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____13966
                       then
                         let uu____13967 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____13967 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___158_13976 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___158_13976.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___158_13976.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___158_13976.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___158_13976.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___158_13976.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___158_13976.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___158_13976.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___158_13976.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____13978 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____14006 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____14006) &&
                       (let uu____14010 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____14010))
                      &&
                      (let uu____14017 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____14017 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___116_14029 =
                             match uu___116_14029 with
                             | FStar_Syntax_Syntax.Delta_constant  -> true
                             | FStar_Syntax_Syntax.Delta_defined_at_level
                                 uu____14030 -> true
                             | uu____14031 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____14032 -> false)
                     in
                  let uu____14033 = as_refinement should_delta env wl t1  in
                  (match uu____14033 with
                   | (x11,phi1) ->
                       let uu____14046 = as_refinement should_delta env wl t2
                          in
                       (match uu____14046 with
                        | (x21,phi21) ->
                            let uu____14059 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____14059 with
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
                                   let uu____14125 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____14125
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____14137 =
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
                                   let uu____14148 =
                                     let uu____14153 =
                                       let uu____14160 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____14160]  in
                                     mk_t_problem wl1 uu____14153 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____14148 with
                                    | (ref_prob,wl2) ->
                                        let uu____14175 =
                                          solve env1
                                            (let uu___159_14177 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___159_14177.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___159_14177.smt_ok);
                                               tcenv = (uu___159_14177.tcenv);
                                               wl_implicits =
                                                 (uu___159_14177.wl_implicits)
                                             })
                                           in
                                        (match uu____14175 with
                                         | Failed uu____14184 -> fallback ()
                                         | Success uu____14189 ->
                                             let guard =
                                               let uu____14197 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____14197
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___160_14206 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___160_14206.attempting);
                                                 wl_deferred =
                                                   (uu___160_14206.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___160_14206.defer_ok);
                                                 smt_ok =
                                                   (uu___160_14206.smt_ok);
                                                 tcenv =
                                                   (uu___160_14206.tcenv);
                                                 wl_implicits =
                                                   (uu___160_14206.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____14208,FStar_Syntax_Syntax.Tm_uvar uu____14209) ->
                  let uu____14210 = destruct_flex_t t1  in
                  let uu____14211 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14210 uu____14211
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14212;
                    FStar_Syntax_Syntax.pos = uu____14213;
                    FStar_Syntax_Syntax.vars = uu____14214;_},uu____14215),FStar_Syntax_Syntax.Tm_uvar
                 uu____14216) ->
                  let uu____14237 = destruct_flex_t t1  in
                  let uu____14238 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14237 uu____14238
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____14239,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14240;
                    FStar_Syntax_Syntax.pos = uu____14241;
                    FStar_Syntax_Syntax.vars = uu____14242;_},uu____14243))
                  ->
                  let uu____14264 = destruct_flex_t t1  in
                  let uu____14265 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14264 uu____14265
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14266;
                    FStar_Syntax_Syntax.pos = uu____14267;
                    FStar_Syntax_Syntax.vars = uu____14268;_},uu____14269),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14270;
                    FStar_Syntax_Syntax.pos = uu____14271;
                    FStar_Syntax_Syntax.vars = uu____14272;_},uu____14273))
                  ->
                  let uu____14314 = destruct_flex_t t1  in
                  let uu____14315 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____14314 uu____14315
              | (FStar_Syntax_Syntax.Tm_uvar uu____14316,uu____14317) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____14318 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____14318 t2
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14319;
                    FStar_Syntax_Syntax.pos = uu____14320;
                    FStar_Syntax_Syntax.vars = uu____14321;_},uu____14322),uu____14323)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____14344 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____14344 t2
              | (uu____14345,FStar_Syntax_Syntax.Tm_uvar uu____14346) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____14347,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14348;
                    FStar_Syntax_Syntax.pos = uu____14349;
                    FStar_Syntax_Syntax.vars = uu____14350;_},uu____14351))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____14372,FStar_Syntax_Syntax.Tm_type uu____14373) ->
                  solve_t' env
                    (let uu___161_14375 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___161_14375.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___161_14375.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___161_14375.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___161_14375.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___161_14375.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___161_14375.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___161_14375.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___161_14375.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___161_14375.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14376;
                    FStar_Syntax_Syntax.pos = uu____14377;
                    FStar_Syntax_Syntax.vars = uu____14378;_},uu____14379),FStar_Syntax_Syntax.Tm_type
                 uu____14380) ->
                  solve_t' env
                    (let uu___161_14402 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___161_14402.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___161_14402.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___161_14402.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___161_14402.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___161_14402.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___161_14402.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___161_14402.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___161_14402.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___161_14402.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____14403,FStar_Syntax_Syntax.Tm_arrow uu____14404) ->
                  solve_t' env
                    (let uu___161_14418 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___161_14418.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___161_14418.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___161_14418.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___161_14418.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___161_14418.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___161_14418.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___161_14418.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___161_14418.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___161_14418.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14419;
                    FStar_Syntax_Syntax.pos = uu____14420;
                    FStar_Syntax_Syntax.vars = uu____14421;_},uu____14422),FStar_Syntax_Syntax.Tm_arrow
                 uu____14423) ->
                  solve_t' env
                    (let uu___161_14457 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___161_14457.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___161_14457.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___161_14457.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___161_14457.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___161_14457.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___161_14457.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___161_14457.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___161_14457.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___161_14457.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____14458,uu____14459) ->
                  if wl.defer_ok
                  then
                    solve env (defer "flex-rigid subtyping deferred" orig wl)
                  else
                    (let new_rel = problem.FStar_TypeChecker_Common.relation
                        in
                     let uu____14462 =
                       let uu____14463 = is_top_level_prob orig  in
                       FStar_All.pipe_left Prims.op_Negation uu____14463  in
                     if uu____14462
                     then
                       let uu____14464 =
                         FStar_All.pipe_left
                           (fun _0_26  ->
                              FStar_TypeChecker_Common.TProb _0_26)
                           (let uu___162_14468 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___162_14468.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___162_14468.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation = new_rel;
                              FStar_TypeChecker_Common.rhs =
                                (uu___162_14468.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___162_14468.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___162_14468.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___162_14468.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___162_14468.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___162_14468.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___162_14468.FStar_TypeChecker_Common.rank)
                            })
                          in
                       let uu____14469 = destruct_flex_t t1  in
                       solve_t_flex_rigid_eq env uu____14464 wl uu____14469
                         t2
                     else
                       (let uu____14471 = base_and_refinement env t2  in
                        match uu____14471 with
                        | (t_base,ref_opt) ->
                            (match ref_opt with
                             | FStar_Pervasives_Native.None  ->
                                 let uu____14500 =
                                   FStar_All.pipe_left
                                     (fun _0_27  ->
                                        FStar_TypeChecker_Common.TProb _0_27)
                                     (let uu___163_14504 = problem  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___163_14504.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___163_14504.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          new_rel;
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___163_14504.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___163_14504.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___163_14504.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.logical_guard_uvar
                                          =
                                          (uu___163_14504.FStar_TypeChecker_Common.logical_guard_uvar);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___163_14504.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___163_14504.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___163_14504.FStar_TypeChecker_Common.rank)
                                      })
                                    in
                                 let uu____14505 = destruct_flex_t t1  in
                                 solve_t_flex_rigid_eq env uu____14500 wl
                                   uu____14505 t_base
                             | FStar_Pervasives_Native.Some (y,phi) ->
                                 let y' =
                                   let uu___164_14513 = y  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___164_14513.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___164_14513.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }  in
                                 let impl =
                                   guard_on_element wl problem y' phi  in
                                 let uu____14517 =
                                   mk_t_problem wl [] orig t1 new_rel
                                     y.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "flex-rigid: base type"
                                    in
                                 (match uu____14517 with
                                  | (base_prob,wl1) ->
                                      let guard =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) impl
                                         in
                                      let wl2 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl1
                                         in
                                      solve env (attempt [base_prob] wl2)))))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14532;
                    FStar_Syntax_Syntax.pos = uu____14533;
                    FStar_Syntax_Syntax.vars = uu____14534;_},uu____14535),uu____14536)
                  ->
                  if wl.defer_ok
                  then
                    solve env (defer "flex-rigid subtyping deferred" orig wl)
                  else
                    (let new_rel = problem.FStar_TypeChecker_Common.relation
                        in
                     let uu____14559 =
                       let uu____14560 = is_top_level_prob orig  in
                       FStar_All.pipe_left Prims.op_Negation uu____14560  in
                     if uu____14559
                     then
                       let uu____14561 =
                         FStar_All.pipe_left
                           (fun _0_28  ->
                              FStar_TypeChecker_Common.TProb _0_28)
                           (let uu___162_14565 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___162_14565.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___162_14565.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation = new_rel;
                              FStar_TypeChecker_Common.rhs =
                                (uu___162_14565.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___162_14565.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___162_14565.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___162_14565.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___162_14565.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___162_14565.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___162_14565.FStar_TypeChecker_Common.rank)
                            })
                          in
                       let uu____14566 = destruct_flex_t t1  in
                       solve_t_flex_rigid_eq env uu____14561 wl uu____14566
                         t2
                     else
                       (let uu____14568 = base_and_refinement env t2  in
                        match uu____14568 with
                        | (t_base,ref_opt) ->
                            (match ref_opt with
                             | FStar_Pervasives_Native.None  ->
                                 let uu____14597 =
                                   FStar_All.pipe_left
                                     (fun _0_29  ->
                                        FStar_TypeChecker_Common.TProb _0_29)
                                     (let uu___163_14601 = problem  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___163_14601.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___163_14601.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          new_rel;
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___163_14601.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___163_14601.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___163_14601.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.logical_guard_uvar
                                          =
                                          (uu___163_14601.FStar_TypeChecker_Common.logical_guard_uvar);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___163_14601.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___163_14601.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___163_14601.FStar_TypeChecker_Common.rank)
                                      })
                                    in
                                 let uu____14602 = destruct_flex_t t1  in
                                 solve_t_flex_rigid_eq env uu____14597 wl
                                   uu____14602 t_base
                             | FStar_Pervasives_Native.Some (y,phi) ->
                                 let y' =
                                   let uu___164_14610 = y  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___164_14610.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___164_14610.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }  in
                                 let impl =
                                   guard_on_element wl problem y' phi  in
                                 let uu____14614 =
                                   mk_t_problem wl [] orig t1 new_rel
                                     y.FStar_Syntax_Syntax.sort
                                     problem.FStar_TypeChecker_Common.element
                                     "flex-rigid: base type"
                                    in
                                 (match uu____14614 with
                                  | (base_prob,wl1) ->
                                      let guard =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) impl
                                         in
                                      let wl2 =
                                        solve_prob orig
                                          (FStar_Pervasives_Native.Some guard)
                                          [] wl1
                                         in
                                      solve env (attempt [base_prob] wl2)))))
              | (uu____14629,FStar_Syntax_Syntax.Tm_uvar uu____14630) ->
                  if wl.defer_ok
                  then
                    solve env (defer "rigid-flex subtyping deferred" orig wl)
                  else
                    (let uu____14632 = base_and_refinement env t1  in
                     match uu____14632 with
                     | (t_base,uu____14644) ->
                         solve_t env
                           (let uu___165_14658 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___165_14658.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs = t_base;
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___165_14658.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___165_14658.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___165_14658.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___165_14658.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___165_14658.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___165_14658.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___165_14658.FStar_TypeChecker_Common.rank)
                            }) wl)
              | (uu____14659,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____14660;
                    FStar_Syntax_Syntax.pos = uu____14661;
                    FStar_Syntax_Syntax.vars = uu____14662;_},uu____14663))
                  ->
                  if wl.defer_ok
                  then
                    solve env (defer "rigid-flex subtyping deferred" orig wl)
                  else
                    (let uu____14685 = base_and_refinement env t1  in
                     match uu____14685 with
                     | (t_base,uu____14697) ->
                         solve_t env
                           (let uu___165_14711 = problem  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___165_14711.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs = t_base;
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___165_14711.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___165_14711.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___165_14711.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___165_14711.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___165_14711.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___165_14711.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___165_14711.FStar_TypeChecker_Common.rank)
                            }) wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____14712,uu____14713) ->
                  let t21 =
                    let uu____14721 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____14721  in
                  solve_t env
                    (let uu___166_14747 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___166_14747.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___166_14747.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___166_14747.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___166_14747.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___166_14747.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___166_14747.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___166_14747.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___166_14747.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___166_14747.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____14748,FStar_Syntax_Syntax.Tm_refine uu____14749) ->
                  let t11 =
                    let uu____14757 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____14757  in
                  solve_t env
                    (let uu___167_14783 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___167_14783.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___167_14783.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___167_14783.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___167_14783.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___167_14783.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___167_14783.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___167_14783.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___167_14783.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___167_14783.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____14860 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____14860 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____15081 = br1  in
                             (match uu____15081 with
                              | (p1,w1,uu____15106) ->
                                  let uu____15123 = br2  in
                                  (match uu____15123 with
                                   | (p2,w2,uu____15142) ->
                                       let uu____15147 =
                                         let uu____15148 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____15148  in
                                       if uu____15147
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____15164 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____15164 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____15197 = br2  in
                                              (match uu____15197 with
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
                                                     let uu____15232 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____15232
                                                      in
                                                   let uu____15243 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____15266,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____15283) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____15326 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____15326
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____15243
                                                     (fun uu____15368  ->
                                                        match uu____15368
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____15389 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____15389
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____15404
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____15404
                                                                   (fun
                                                                    uu____15428
                                                                     ->
                                                                    match uu____15428
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
                         | uu____15513 -> FStar_Pervasives_Native.None  in
                       let uu____15550 = solve_branches wl1 brs1 brs2  in
                       (match uu____15550 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____15581,uu____15582) ->
                  let head1 =
                    let uu____15606 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15606
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____15640 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____15640
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____15674 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____15674
                    then
                      let uu____15675 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____15676 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____15677 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____15675 uu____15676 uu____15677
                    else ());
                   (let uu____15679 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____15679
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____15686 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____15686
                       then
                         let uu____15687 =
                           let uu____15694 =
                             let uu____15695 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____15695 = FStar_Syntax_Util.Equal  in
                           if uu____15694
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____15705 = mk_eq2 wl orig t1 t2  in
                              match uu____15705 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____15687 with
                         | (guard,wl1) ->
                             let uu____15726 = solve_prob orig guard [] wl1
                                in
                             solve env uu____15726
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____15729,uu____15730) ->
                  let head1 =
                    let uu____15738 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15738
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____15772 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____15772
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____15806 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____15806
                    then
                      let uu____15807 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____15808 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____15809 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____15807 uu____15808 uu____15809
                    else ());
                   (let uu____15811 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____15811
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____15818 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____15818
                       then
                         let uu____15819 =
                           let uu____15826 =
                             let uu____15827 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____15827 = FStar_Syntax_Util.Equal  in
                           if uu____15826
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____15837 = mk_eq2 wl orig t1 t2  in
                              match uu____15837 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____15819 with
                         | (guard,wl1) ->
                             let uu____15858 = solve_prob orig guard [] wl1
                                in
                             solve env uu____15858
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____15861,uu____15862) ->
                  let head1 =
                    let uu____15864 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15864
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____15898 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____15898
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____15932 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____15932
                    then
                      let uu____15933 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____15934 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____15935 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____15933 uu____15934 uu____15935
                    else ());
                   (let uu____15937 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____15937
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____15944 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____15944
                       then
                         let uu____15945 =
                           let uu____15952 =
                             let uu____15953 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____15953 = FStar_Syntax_Util.Equal  in
                           if uu____15952
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____15963 = mk_eq2 wl orig t1 t2  in
                              match uu____15963 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____15945 with
                         | (guard,wl1) ->
                             let uu____15984 = solve_prob orig guard [] wl1
                                in
                             solve env uu____15984
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____15987,uu____15988) ->
                  let head1 =
                    let uu____15990 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____15990
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16024 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16024
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16058 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16058
                    then
                      let uu____16059 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16060 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16061 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16059 uu____16060 uu____16061
                    else ());
                   (let uu____16063 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16063
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16070 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16070
                       then
                         let uu____16071 =
                           let uu____16078 =
                             let uu____16079 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16079 = FStar_Syntax_Util.Equal  in
                           if uu____16078
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16089 = mk_eq2 wl orig t1 t2  in
                              match uu____16089 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16071 with
                         | (guard,wl1) ->
                             let uu____16110 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16110
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____16113,uu____16114) ->
                  let head1 =
                    let uu____16116 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16116
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16150 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16150
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16184 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16184
                    then
                      let uu____16185 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16186 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16187 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16185 uu____16186 uu____16187
                    else ());
                   (let uu____16189 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16189
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16196 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16196
                       then
                         let uu____16197 =
                           let uu____16204 =
                             let uu____16205 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16205 = FStar_Syntax_Util.Equal  in
                           if uu____16204
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16215 = mk_eq2 wl orig t1 t2  in
                              match uu____16215 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16197 with
                         | (guard,wl1) ->
                             let uu____16236 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16236
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____16239,uu____16240) ->
                  let head1 =
                    let uu____16256 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16256
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16290 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16290
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16324 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16324
                    then
                      let uu____16325 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16326 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16327 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16325 uu____16326 uu____16327
                    else ());
                   (let uu____16329 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16329
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16336 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16336
                       then
                         let uu____16337 =
                           let uu____16344 =
                             let uu____16345 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16345 = FStar_Syntax_Util.Equal  in
                           if uu____16344
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16355 = mk_eq2 wl orig t1 t2  in
                              match uu____16355 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16337 with
                         | (guard,wl1) ->
                             let uu____16376 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16376
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16379,FStar_Syntax_Syntax.Tm_match uu____16380) ->
                  let head1 =
                    let uu____16404 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16404
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16438 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16438
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16472 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16472
                    then
                      let uu____16473 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16474 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16475 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16473 uu____16474 uu____16475
                    else ());
                   (let uu____16477 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16477
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16484 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16484
                       then
                         let uu____16485 =
                           let uu____16492 =
                             let uu____16493 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16493 = FStar_Syntax_Util.Equal  in
                           if uu____16492
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16503 = mk_eq2 wl orig t1 t2  in
                              match uu____16503 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16485 with
                         | (guard,wl1) ->
                             let uu____16524 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16524
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16527,FStar_Syntax_Syntax.Tm_uinst uu____16528) ->
                  let head1 =
                    let uu____16536 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16536
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16570 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16570
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16604 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16604
                    then
                      let uu____16605 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16606 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16607 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16605 uu____16606 uu____16607
                    else ());
                   (let uu____16609 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16609
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16616 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16616
                       then
                         let uu____16617 =
                           let uu____16624 =
                             let uu____16625 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16625 = FStar_Syntax_Util.Equal  in
                           if uu____16624
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16635 = mk_eq2 wl orig t1 t2  in
                              match uu____16635 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16617 with
                         | (guard,wl1) ->
                             let uu____16656 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16656
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16659,FStar_Syntax_Syntax.Tm_name uu____16660) ->
                  let head1 =
                    let uu____16662 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16662
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16696 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16696
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16730 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16730
                    then
                      let uu____16731 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16732 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16733 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16731 uu____16732 uu____16733
                    else ());
                   (let uu____16735 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16735
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16742 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16742
                       then
                         let uu____16743 =
                           let uu____16750 =
                             let uu____16751 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16751 = FStar_Syntax_Util.Equal  in
                           if uu____16750
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16761 = mk_eq2 wl orig t1 t2  in
                              match uu____16761 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16743 with
                         | (guard,wl1) ->
                             let uu____16782 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16782
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16785,FStar_Syntax_Syntax.Tm_constant uu____16786) ->
                  let head1 =
                    let uu____16788 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16788
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16822 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16822
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16856 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16856
                    then
                      let uu____16857 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16858 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16859 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16857 uu____16858 uu____16859
                    else ());
                   (let uu____16861 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16861
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16868 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16868
                       then
                         let uu____16869 =
                           let uu____16876 =
                             let uu____16877 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16877 = FStar_Syntax_Util.Equal  in
                           if uu____16876
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16887 = mk_eq2 wl orig t1 t2  in
                              match uu____16887 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16869 with
                         | (guard,wl1) ->
                             let uu____16908 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16908
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____16911,FStar_Syntax_Syntax.Tm_fvar uu____16912) ->
                  let head1 =
                    let uu____16914 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16914
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16948 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16948
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16982 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16982
                    then
                      let uu____16983 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16984 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16985 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16983 uu____16984 uu____16985
                    else ());
                   (let uu____16987 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16987
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16994 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16994
                       then
                         let uu____16995 =
                           let uu____17002 =
                             let uu____17003 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17003 = FStar_Syntax_Util.Equal  in
                           if uu____17002
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17013 = mk_eq2 wl orig t1 t2  in
                              match uu____17013 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16995 with
                         | (guard,wl1) ->
                             let uu____17034 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17034
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17037,FStar_Syntax_Syntax.Tm_app uu____17038) ->
                  let head1 =
                    let uu____17054 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17054
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17088 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17088
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17122 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17122
                    then
                      let uu____17123 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17124 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17125 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17123 uu____17124 uu____17125
                    else ());
                   (let uu____17127 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17127
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17134 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17134
                       then
                         let uu____17135 =
                           let uu____17142 =
                             let uu____17143 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17143 = FStar_Syntax_Util.Equal  in
                           if uu____17142
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17153 = mk_eq2 wl orig t1 t2  in
                              match uu____17153 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17135 with
                         | (guard,wl1) ->
                             let uu____17174 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17174
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____17177,FStar_Syntax_Syntax.Tm_let uu____17178) ->
                  let uu____17203 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____17203
                  then
                    let uu____17204 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____17204
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____17206,uu____17207) ->
                  let uu____17220 =
                    let uu____17225 =
                      let uu____17226 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____17227 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____17228 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____17229 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____17226 uu____17227 uu____17228 uu____17229
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____17225)
                     in
                  FStar_Errors.raise_error uu____17220
                    t1.FStar_Syntax_Syntax.pos
              | (uu____17230,FStar_Syntax_Syntax.Tm_let uu____17231) ->
                  let uu____17244 =
                    let uu____17249 =
                      let uu____17250 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____17251 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____17252 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____17253 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____17250 uu____17251 uu____17252 uu____17253
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____17249)
                     in
                  FStar_Errors.raise_error uu____17244
                    t1.FStar_Syntax_Syntax.pos
              | uu____17254 -> giveup env "head tag mismatch" orig))))

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
          (let uu____17313 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____17313
           then
             let uu____17314 =
               let uu____17315 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____17315  in
             let uu____17316 =
               let uu____17317 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____17317  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____17314 uu____17316
           else ());
          (let uu____17319 =
             let uu____17320 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____17320  in
           if uu____17319
           then
             let uu____17321 =
               let uu____17322 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____17323 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____17322 uu____17323
                in
             giveup env uu____17321 orig
           else
             (let uu____17325 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____17325 with
              | (ret_sub_prob,wl1) ->
                  let uu____17332 =
                    FStar_List.fold_right2
                      (fun uu____17365  ->
                         fun uu____17366  ->
                           fun uu____17367  ->
                             match (uu____17365, uu____17366, uu____17367)
                             with
                             | ((a1,uu____17403),(a2,uu____17405),(arg_sub_probs,wl2))
                                 ->
                                 let uu____17426 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____17426 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____17332 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____17455 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____17455  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____17485 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____17488)::[] -> wp1
              | uu____17505 ->
                  let uu____17514 =
                    let uu____17515 =
                      let uu____17516 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____17516  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____17515
                     in
                  failwith uu____17514
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____17522 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____17522]
              | x -> x  in
            let uu____17524 =
              let uu____17533 =
                let uu____17540 =
                  let uu____17541 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____17541 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____17540  in
              [uu____17533]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____17524;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____17554 = lift_c1 ()  in solve_eq uu____17554 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_17560  ->
                       match uu___117_17560 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____17561 -> false))
                in
             let uu____17562 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____17596)::uu____17597,(wp2,uu____17599)::uu____17600)
                   -> (wp1, wp2)
               | uu____17657 ->
                   let uu____17678 =
                     let uu____17683 =
                       let uu____17684 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____17685 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____17684 uu____17685
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____17683)
                      in
                   FStar_Errors.raise_error uu____17678
                     env.FStar_TypeChecker_Env.range
                in
             match uu____17562 with
             | (wpc1,wpc2) ->
                 let uu____17704 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____17704
                 then
                   let uu____17707 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____17707 wl
                 else
                   (let uu____17709 =
                      let uu____17716 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____17716  in
                    match uu____17709 with
                    | (c2_decl,qualifiers) ->
                        let uu____17737 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____17737
                        then
                          let c1_repr =
                            let uu____17741 =
                              let uu____17742 =
                                let uu____17743 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____17743  in
                              let uu____17744 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____17742 uu____17744
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____17741
                             in
                          let c2_repr =
                            let uu____17746 =
                              let uu____17747 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____17748 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____17747 uu____17748
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____17746
                             in
                          let uu____17749 =
                            let uu____17754 =
                              let uu____17755 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____17756 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____17755 uu____17756
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____17754
                             in
                          (match uu____17749 with
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
                                 ((let uu____17770 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____17770
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____17773 =
                                     let uu____17780 =
                                       let uu____17781 =
                                         let uu____17796 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____17799 =
                                           let uu____17808 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____17815 =
                                             let uu____17824 =
                                               let uu____17831 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____17831
                                                in
                                             [uu____17824]  in
                                           uu____17808 :: uu____17815  in
                                         (uu____17796, uu____17799)  in
                                       FStar_Syntax_Syntax.Tm_app uu____17781
                                        in
                                     FStar_Syntax_Syntax.mk uu____17780  in
                                   uu____17773 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____17872 =
                                    let uu____17879 =
                                      let uu____17880 =
                                        let uu____17895 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____17898 =
                                          let uu____17907 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____17914 =
                                            let uu____17923 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____17930 =
                                              let uu____17939 =
                                                let uu____17946 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____17946
                                                 in
                                              [uu____17939]  in
                                            uu____17923 :: uu____17930  in
                                          uu____17907 :: uu____17914  in
                                        (uu____17895, uu____17898)  in
                                      FStar_Syntax_Syntax.Tm_app uu____17880
                                       in
                                    FStar_Syntax_Syntax.mk uu____17879  in
                                  uu____17872 FStar_Pervasives_Native.None r)
                              in
                           let uu____17990 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____17990 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____17998 =
                                   let uu____18001 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_30  ->
                                        FStar_Pervasives_Native.Some _0_30)
                                     uu____18001
                                    in
                                 solve_prob orig uu____17998 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____18004 = FStar_Util.physical_equality c1 c2  in
        if uu____18004
        then
          let uu____18005 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____18005
        else
          ((let uu____18008 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____18008
            then
              let uu____18009 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____18010 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____18009
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____18010
            else ());
           (let uu____18012 =
              let uu____18021 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____18024 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____18021, uu____18024)  in
            match uu____18012 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18042),FStar_Syntax_Syntax.Total
                    (t2,uu____18044)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____18061 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18061 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____18062,FStar_Syntax_Syntax.Total uu____18063) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18081),FStar_Syntax_Syntax.Total
                    (t2,uu____18083)) ->
                     let uu____18100 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18100 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18102),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18104)) ->
                     let uu____18121 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18121 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18123),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18125)) ->
                     let uu____18142 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18142 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____18143,FStar_Syntax_Syntax.Comp uu____18144) ->
                     let uu____18153 =
                       let uu___168_18156 = problem  in
                       let uu____18159 =
                         let uu____18160 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18160
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___168_18156.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18159;
                         FStar_TypeChecker_Common.relation =
                           (uu___168_18156.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___168_18156.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___168_18156.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___168_18156.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___168_18156.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___168_18156.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___168_18156.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___168_18156.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18153 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____18161,FStar_Syntax_Syntax.Comp uu____18162) ->
                     let uu____18171 =
                       let uu___168_18174 = problem  in
                       let uu____18177 =
                         let uu____18178 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18178
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___168_18174.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18177;
                         FStar_TypeChecker_Common.relation =
                           (uu___168_18174.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___168_18174.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___168_18174.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___168_18174.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___168_18174.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___168_18174.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___168_18174.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___168_18174.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18171 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18179,FStar_Syntax_Syntax.GTotal uu____18180) ->
                     let uu____18189 =
                       let uu___169_18192 = problem  in
                       let uu____18195 =
                         let uu____18196 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18196
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___169_18192.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___169_18192.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___169_18192.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18195;
                         FStar_TypeChecker_Common.element =
                           (uu___169_18192.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___169_18192.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___169_18192.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___169_18192.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___169_18192.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___169_18192.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18189 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18197,FStar_Syntax_Syntax.Total uu____18198) ->
                     let uu____18207 =
                       let uu___169_18210 = problem  in
                       let uu____18213 =
                         let uu____18214 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18214
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___169_18210.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___169_18210.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___169_18210.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18213;
                         FStar_TypeChecker_Common.element =
                           (uu___169_18210.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___169_18210.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___169_18210.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___169_18210.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___169_18210.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___169_18210.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18207 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18215,FStar_Syntax_Syntax.Comp uu____18216) ->
                     let uu____18217 =
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
                     if uu____18217
                     then
                       let uu____18218 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____18218 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____18222 =
                            let uu____18227 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____18227
                            then (c1_comp, c2_comp)
                            else
                              (let uu____18233 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____18234 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____18233, uu____18234))
                             in
                          match uu____18222 with
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
                           (let uu____18241 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____18241
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____18243 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____18243 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____18246 =
                                  let uu____18247 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____18248 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____18247 uu____18248
                                   in
                                giveup env uu____18246 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____18255 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____18288  ->
              match uu____18288 with
              | (uu____18299,tm,uu____18301,uu____18302,uu____18303) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____18255 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____18336 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____18336 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____18354 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____18382  ->
                match uu____18382 with
                | (u1,u2) ->
                    let uu____18389 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____18390 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____18389 uu____18390))
         in
      FStar_All.pipe_right uu____18354 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____18417,[])) -> "{}"
      | uu____18442 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____18465 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____18465
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____18468 =
              FStar_List.map
                (fun uu____18478  ->
                   match uu____18478 with
                   | (uu____18483,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____18468 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____18488 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____18488 imps
  
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
                  let uu____18541 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ExplainRel")
                     in
                  if uu____18541
                  then
                    let uu____18542 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____18543 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____18542
                      (rel_to_string rel) uu____18543
                  else "TOP"  in
                let uu____18545 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____18545 with
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
              let uu____18602 =
                let uu____18605 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                  uu____18605
                 in
              FStar_Syntax_Syntax.new_bv uu____18602 t1  in
            let uu____18608 =
              let uu____18613 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____18613
               in
            match uu____18608 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____18669 = FStar_Options.eager_inference ()  in
          if uu____18669
          then
            let uu___170_18670 = probs  in
            {
              attempting = (uu___170_18670.attempting);
              wl_deferred = (uu___170_18670.wl_deferred);
              ctr = (uu___170_18670.ctr);
              defer_ok = false;
              smt_ok = (uu___170_18670.smt_ok);
              tcenv = (uu___170_18670.tcenv);
              wl_implicits = (uu___170_18670.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____18690 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____18690
              then
                let uu____18691 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____18691
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
          ((let uu____18713 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____18713
            then
              let uu____18714 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____18714
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____18718 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____18718
             then
               let uu____18719 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____18719
             else ());
            (let f2 =
               let uu____18722 =
                 let uu____18723 = FStar_Syntax_Util.unmeta f1  in
                 uu____18723.FStar_Syntax_Syntax.n  in
               match uu____18722 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____18727 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___171_18728 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___171_18728.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___171_18728.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___171_18728.FStar_TypeChecker_Env.implicits)
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
            let uu____18842 =
              let uu____18843 =
                let uu____18844 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_32  -> FStar_TypeChecker_Common.NonTrivial _0_32)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____18844;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____18843  in
            FStar_All.pipe_left
              (fun _0_33  -> FStar_Pervasives_Native.Some _0_33) uu____18842
  
let with_guard_no_simp :
  'Auu____18859 .
    'Auu____18859 ->
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
            let uu____18882 =
              let uu____18883 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_34  -> FStar_TypeChecker_Common.NonTrivial _0_34)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____18883;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____18882
  
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
          (let uu____18923 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____18923
           then
             let uu____18924 = FStar_Syntax_Print.term_to_string t1  in
             let uu____18925 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____18924
               uu____18925
           else ());
          (let uu____18927 =
             let uu____18932 = empty_worklist env  in
             let uu____18933 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____18932 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____18933
              in
           match uu____18927 with
           | (prob,wl) ->
               let g =
                 let uu____18941 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____18961  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____18941  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____19005 = try_teq true env t1 t2  in
        match uu____19005 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____19009 = FStar_TypeChecker_Env.get_range env  in
              let uu____19010 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____19009 uu____19010);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____19017 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____19017
              then
                let uu____19018 = FStar_Syntax_Print.term_to_string t1  in
                let uu____19019 = FStar_Syntax_Print.term_to_string t2  in
                let uu____19020 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____19018
                  uu____19019 uu____19020
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
          let uu____19042 = FStar_TypeChecker_Env.get_range env  in
          let uu____19043 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____19042 uu____19043
  
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
        (let uu____19068 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____19068
         then
           let uu____19069 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____19070 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____19069 uu____19070
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____19073 =
           let uu____19080 = empty_worklist env  in
           let uu____19081 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____19080 env c1 rel c2 FStar_Pervasives_Native.None
             uu____19081 "sub_comp"
            in
         match uu____19073 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____19091 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____19111  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____19091)
  
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
      fun uu____19166  ->
        match uu____19166 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____19209 =
                 let uu____19214 =
                   let uu____19215 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____19216 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____19215 uu____19216
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____19214)  in
               let uu____19217 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____19209 uu____19217)
               in
            let equiv1 v1 v' =
              let uu____19229 =
                let uu____19234 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____19235 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____19234, uu____19235)  in
              match uu____19229 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____19254 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____19284 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____19284 with
                      | FStar_Syntax_Syntax.U_unif uu____19291 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____19320  ->
                                    match uu____19320 with
                                    | (u,v') ->
                                        let uu____19329 = equiv1 v1 v'  in
                                        if uu____19329
                                        then
                                          let uu____19332 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____19332 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____19348 -> []))
               in
            let uu____19353 =
              let wl =
                let uu___172_19357 = empty_worklist env  in
                {
                  attempting = (uu___172_19357.attempting);
                  wl_deferred = (uu___172_19357.wl_deferred);
                  ctr = (uu___172_19357.ctr);
                  defer_ok = false;
                  smt_ok = (uu___172_19357.smt_ok);
                  tcenv = (uu___172_19357.tcenv);
                  wl_implicits = (uu___172_19357.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____19375  ->
                      match uu____19375 with
                      | (lb,v1) ->
                          let uu____19382 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____19382 with
                           | USolved wl1 -> ()
                           | uu____19384 -> fail1 lb v1)))
               in
            let rec check_ineq uu____19394 =
              match uu____19394 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____19403) -> true
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
                      uu____19426,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____19428,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____19439) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____19446,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____19454 -> false)
               in
            let uu____19459 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____19474  ->
                      match uu____19474 with
                      | (u,v1) ->
                          let uu____19481 = check_ineq (u, v1)  in
                          if uu____19481
                          then true
                          else
                            ((let uu____19484 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____19484
                              then
                                let uu____19485 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____19486 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____19485
                                  uu____19486
                              else ());
                             false)))
               in
            if uu____19459
            then ()
            else
              ((let uu____19490 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____19490
                then
                  ((let uu____19492 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____19492);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____19502 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____19502))
                else ());
               (let uu____19512 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____19512))
  
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
        let fail1 uu____19579 =
          match uu____19579 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___173_19600 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___173_19600.attempting);
            wl_deferred = (uu___173_19600.wl_deferred);
            ctr = (uu___173_19600.ctr);
            defer_ok;
            smt_ok = (uu___173_19600.smt_ok);
            tcenv = (uu___173_19600.tcenv);
            wl_implicits = (uu___173_19600.wl_implicits)
          }  in
        (let uu____19602 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____19602
         then
           let uu____19603 = FStar_Util.string_of_bool defer_ok  in
           let uu____19604 = wl_to_string wl  in
           let uu____19605 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____19603 uu____19604 uu____19605
         else ());
        (let g1 =
           let uu____19618 = solve_and_commit env wl fail1  in
           match uu____19618 with
           | FStar_Pervasives_Native.Some
               (uu____19625::uu____19626,uu____19627) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___174_19652 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___174_19652.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___174_19652.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____19663 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___175_19671 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___175_19671.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___175_19671.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___175_19671.FStar_TypeChecker_Env.implicits)
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
    let uu____19719 = FStar_ST.op_Bang last_proof_ns  in
    match uu____19719 with
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
            let uu___176_19842 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___176_19842.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___176_19842.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___176_19842.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____19843 =
            let uu____19844 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____19844  in
          if uu____19843
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____19852 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____19853 =
                       let uu____19854 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____19854
                        in
                     FStar_Errors.diag uu____19852 uu____19853)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____19858 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____19859 =
                        let uu____19860 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____19860
                         in
                      FStar_Errors.diag uu____19858 uu____19859)
                   else ();
                   (let uu____19863 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____19863 "discharge_guard'"
                      env vc1);
                   (let uu____19864 = check_trivial vc1  in
                    match uu____19864 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____19871 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____19872 =
                                let uu____19873 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____19873
                                 in
                              FStar_Errors.diag uu____19871 uu____19872)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____19878 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____19879 =
                                let uu____19880 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____19880
                                 in
                              FStar_Errors.diag uu____19878 uu____19879)
                           else ();
                           (let vcs =
                              let uu____19891 = FStar_Options.use_tactics ()
                                 in
                              if uu____19891
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____19910  ->
                                     (let uu____19912 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____19912);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____19914 =
                                   let uu____19921 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____19921)  in
                                 [uu____19914])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____19955  ->
                                    match uu____19955 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____19966 = check_trivial goal1
                                           in
                                        (match uu____19966 with
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
                                                (let uu____19974 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____19975 =
                                                   let uu____19976 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____19977 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____19976 uu____19977
                                                    in
                                                 FStar_Errors.diag
                                                   uu____19974 uu____19975)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____19980 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____19981 =
                                                   let uu____19982 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____19982
                                                    in
                                                 FStar_Errors.diag
                                                   uu____19980 uu____19981)
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
      let uu____19996 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____19996 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____20003 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____20003
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____20014 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____20014 with
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
            let uu____20047 = FStar_Syntax_Util.head_and_args u  in
            match uu____20047 with
            | (hd1,uu____20061) ->
                let uu____20078 =
                  let uu____20079 = FStar_Syntax_Subst.compress u  in
                  uu____20079.FStar_Syntax_Syntax.n  in
                (match uu____20078 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____20082 -> true
                 | uu____20083 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____20103 = acc  in
            match uu____20103 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____20165 = hd1  in
                     (match uu____20165 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____20182 = unresolved tm  in
                             if uu____20182
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___177_20195 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___177_20195.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___177_20195.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___177_20195.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___177_20195.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___177_20195.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___177_20195.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___177_20195.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___177_20195.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___177_20195.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___177_20195.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___177_20195.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___177_20195.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___177_20195.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___177_20195.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___177_20195.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___177_20195.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___177_20195.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___177_20195.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___177_20195.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___177_20195.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___177_20195.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___177_20195.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___177_20195.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___177_20195.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___177_20195.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___177_20195.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___177_20195.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___177_20195.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___177_20195.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___177_20195.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___177_20195.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___177_20195.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___177_20195.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___177_20195.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___177_20195.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___177_20195.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___177_20195.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___178_20198 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___178_20198.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___178_20198.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___178_20198.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___178_20198.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___178_20198.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___178_20198.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___178_20198.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___178_20198.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___178_20198.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___178_20198.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___178_20198.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___178_20198.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___178_20198.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___178_20198.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___178_20198.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___178_20198.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___178_20198.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___178_20198.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___178_20198.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___178_20198.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___178_20198.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___178_20198.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___178_20198.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___178_20198.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___178_20198.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___178_20198.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___178_20198.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___178_20198.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___178_20198.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___178_20198.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___178_20198.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___178_20198.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___178_20198.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___178_20198.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___178_20198.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___178_20198.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___178_20198.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____20201 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "RelCheck")
                                    in
                                 if uu____20201
                                 then
                                   let uu____20202 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____20203 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____20204 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____20205 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____20202 uu____20203 uu____20204
                                     reason uu____20205
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e ->
                                       ((let uu____20216 =
                                           let uu____20225 =
                                             let uu____20232 =
                                               let uu____20233 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____20234 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____20233 uu____20234
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____20232, r)
                                              in
                                           [uu____20225]  in
                                         FStar_Errors.add_errors uu____20216);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___181_20248 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___181_20248.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___181_20248.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___181_20248.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____20251 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____20258  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____20251 with
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
          let uu___182_20270 = g  in
          let uu____20271 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___182_20270.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___182_20270.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___182_20270.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____20271
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
        let uu____20325 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____20325 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____20336 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____20336
      | (reason,e,ctx_u,r,should_check)::uu____20342 ->
          let uu____20365 =
            let uu____20370 =
              let uu____20371 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____20372 =
                FStar_Syntax_Print.term_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____20373 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____20371 uu____20372 reason uu____20373
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____20370)
             in
          FStar_Errors.raise_error uu____20365 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___183_20384 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___183_20384.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___183_20384.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___183_20384.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____20399 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____20399 with
      | FStar_Pervasives_Native.Some uu____20405 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____20421 = try_teq false env t1 t2  in
        match uu____20421 with
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
        (let uu____20455 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____20455
         then
           let uu____20456 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____20457 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____20456
             uu____20457
         else ());
        (let uu____20459 =
           let uu____20466 = empty_worklist env  in
           new_t_prob uu____20466 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____20459 with
         | (prob,x,wl) ->
             let g =
               let uu____20479 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____20499  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____20479  in
             ((let uu____20529 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____20529
               then
                 let uu____20530 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____20531 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____20532 =
                   let uu____20533 = FStar_Util.must g  in
                   guard_to_string env uu____20533  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____20530 uu____20531 uu____20532
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
        let uu____20567 = check_subtyping env t1 t2  in
        match uu____20567 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____20586 =
              let uu____20587 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____20587 g  in
            FStar_Pervasives_Native.Some uu____20586
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____20605 = check_subtyping env t1 t2  in
        match uu____20605 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____20624 =
              let uu____20625 =
                let uu____20626 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____20626]  in
              close_guard env uu____20625 g  in
            FStar_Pervasives_Native.Some uu____20624
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____20655 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____20655
         then
           let uu____20656 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____20657 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____20656
             uu____20657
         else ());
        (let uu____20659 =
           let uu____20666 = empty_worklist env  in
           new_t_prob uu____20666 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____20659 with
         | (prob,x,wl) ->
             let g =
               let uu____20673 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____20693  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____20673  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____20724 =
                      let uu____20725 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____20725]  in
                    close_guard env uu____20724 g1  in
                  discharge_guard_nosmt env g2))
  