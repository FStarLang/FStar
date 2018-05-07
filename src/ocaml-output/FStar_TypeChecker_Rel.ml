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
          let uu___150_102 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___150_102.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___150_102.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___150_102.FStar_TypeChecker_Env.implicits)
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
          let uu___151_248 = g  in
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
              (uu___151_248.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___151_248.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___151_248.FStar_TypeChecker_Env.implicits)
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
          let uu___152_331 = g  in
          let uu____332 =
            let uu____333 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____333  in
          {
            FStar_TypeChecker_Env.guard_f = uu____332;
            FStar_TypeChecker_Env.deferred =
              (uu___152_331.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___152_331.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___152_331.FStar_TypeChecker_Env.implicits)
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
            let uu___153_499 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___153_499.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___153_499.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___153_499.FStar_TypeChecker_Env.implicits)
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
            let uu___154_559 = g  in
            let uu____560 =
              let uu____561 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____561  in
            {
              FStar_TypeChecker_Env.guard_f = uu____560;
              FStar_TypeChecker_Env.deferred =
                (uu___154_559.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___154_559.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___154_559.FStar_TypeChecker_Env.implicits)
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
                     (FStar_Syntax_Syntax.Tm_uvar
                        (ctx_uvar, ([], FStar_Pervasives_Native.None)))
                     FStar_Pervasives_Native.None r
                    in
                 (ctx_uvar, t,
                   (let uu___155_941 = wl  in
                    {
                      attempting = (uu___155_941.attempting);
                      wl_deferred = (uu___155_941.wl_deferred);
                      ctr = (uu___155_941.ctr);
                      defer_ok = (uu___155_941.defer_ok);
                      smt_ok = (uu___155_941.smt_ok);
                      tcenv = (uu___155_941.tcenv);
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
    match projectee with | Success _0 -> true | uu____1005 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1035 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____1060 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1066 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1072 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
[@@deriving show]
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
[@@deriving show]
type 'a problem_t = 'a FStar_TypeChecker_Common.problem[@@deriving show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___118_1087  ->
    match uu___118_1087 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1093 = FStar_Syntax_Util.head_and_args t  in
    match uu____1093 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1152 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1153 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1167 =
                     let uu____1168 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1168  in
                   FStar_Util.format1 "@<%s>" uu____1167
                in
             let uu____1171 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1152 uu____1153 uu____1171
         | uu____1172 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___119_1182  ->
      match uu___119_1182 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1186 =
            let uu____1189 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1190 =
              let uu____1193 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1194 =
                let uu____1197 =
                  let uu____1200 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1200]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1197
                 in
              uu____1193 :: uu____1194  in
            uu____1189 :: uu____1190  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1186
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1204 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1205 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1206 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1204 uu____1205
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1206
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___120_1216  ->
      match uu___120_1216 with
      | UNIV (u,t) ->
          let x =
            let uu____1220 = FStar_Options.hide_uvar_nums ()  in
            if uu____1220
            then "?"
            else
              (let uu____1222 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1222 FStar_Util.string_of_int)
             in
          let uu____1223 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1223
      | TERM (u,t) ->
          let x =
            let uu____1227 = FStar_Options.hide_uvar_nums ()  in
            if uu____1227
            then "?"
            else
              (let uu____1229 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1229 FStar_Util.string_of_int)
             in
          let uu____1230 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1230
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1245 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1245 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1259 =
      let uu____1262 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1262
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1259 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1275 .
    (FStar_Syntax_Syntax.term,'Auu____1275) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1293 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1311  ->
              match uu____1311 with
              | (x,uu____1317) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1293 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1325 =
      let uu____1326 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1326  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1325;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___156_1358 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___156_1358.wl_deferred);
          ctr = (uu___156_1358.ctr);
          defer_ok = (uu___156_1358.defer_ok);
          smt_ok;
          tcenv = (uu___156_1358.tcenv);
          wl_implicits = (uu___156_1358.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1365 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1365,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___157_1388 = empty_worklist env  in
      let uu____1389 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1389;
        wl_deferred = (uu___157_1388.wl_deferred);
        ctr = (uu___157_1388.ctr);
        defer_ok = (uu___157_1388.defer_ok);
        smt_ok = (uu___157_1388.smt_ok);
        tcenv = (uu___157_1388.tcenv);
        wl_implicits = (uu___157_1388.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___158_1409 = wl  in
        {
          attempting = (uu___158_1409.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___158_1409.ctr);
          defer_ok = (uu___158_1409.defer_ok);
          smt_ok = (uu___158_1409.smt_ok);
          tcenv = (uu___158_1409.tcenv);
          wl_implicits = (uu___158_1409.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___159_1430 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___159_1430.wl_deferred);
        ctr = (uu___159_1430.ctr);
        defer_ok = (uu___159_1430.defer_ok);
        smt_ok = (uu___159_1430.smt_ok);
        tcenv = (uu___159_1430.tcenv);
        wl_implicits = (uu___159_1430.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1447 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1447
         then
           let uu____1448 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1448
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___121_1454  ->
    match uu___121_1454 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1459 .
    'Auu____1459 FStar_TypeChecker_Common.problem ->
      'Auu____1459 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___160_1471 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___160_1471.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___160_1471.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___160_1471.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___160_1471.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___160_1471.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___160_1471.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___160_1471.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1478 .
    'Auu____1478 FStar_TypeChecker_Common.problem ->
      'Auu____1478 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___122_1495  ->
    match uu___122_1495 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___123_1510  ->
    match uu___123_1510 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___161_1516 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___161_1516.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___161_1516.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___161_1516.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___161_1516.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___161_1516.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___161_1516.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___161_1516.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___161_1516.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___161_1516.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___162_1524 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___162_1524.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___162_1524.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___162_1524.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___162_1524.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___162_1524.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___162_1524.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___162_1524.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___162_1524.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___162_1524.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___124_1536  ->
      match uu___124_1536 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___125_1541  ->
    match uu___125_1541 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___126_1552  ->
    match uu___126_1552 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___127_1565  ->
    match uu___127_1565 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___128_1578  ->
    match uu___128_1578 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___129_1589  ->
    match uu___129_1589 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___130_1604  ->
    match uu___130_1604 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1623 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1623) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1651 =
          let uu____1652 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1652  in
        if uu____1651
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1686)::bs ->
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
        let uu____1753 =
          let uu____1754 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1754  in
        if uu____1753
        then ()
        else
          (let uu____1756 =
             let uu____1759 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1759
              in
           def_check_closed_in (p_loc prob) msg uu____1756 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1789 =
         let uu____1790 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1790  in
       if uu____1789
       then ()
       else
         (let uu____1792 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1792));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1804 -> ())
  
let mk_eq2 :
  'Auu____1816 .
    worklist ->
      'Auu____1816 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1845 = FStar_Syntax_Util.type_u ()  in
          match uu____1845 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1857 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type false
                 in
              (match uu____1857 with
               | (uu____1868,tt,wl1) ->
                   let uu____1871 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1871, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___131_1876  ->
    match uu___131_1876 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1892 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1892 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1904  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2002 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2002 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2002 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2002 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2068 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2068  in
                  let uu____2071 =
                    let uu____2078 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2078
                      guard_ty false
                     in
                  match uu____2071 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2099 ->
                            let uu____2106 =
                              let uu____2111 =
                                FStar_List.map
                                  (fun uu____2124  ->
                                     match uu____2124 with
                                     | (x,i) ->
                                         let uu____2135 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2135, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2111  in
                            uu____2106 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2138 =
                        let uu____2141 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2141;
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
                      (uu____2138, wl1)
  
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
                  let uu____2204 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2204 with
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
                  let uu____2281 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2281 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2316 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2316 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2316 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2316 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2367 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2422 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2422]  in
                        let uu____2435 =
                          let uu____2438 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2438  in
                        let uu____2441 =
                          let uu____2444 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2444  in
                        (bs, uu____2435, uu____2441)
                     in
                  match uu____2367 with
                  | (bs,lg_ty,elt) ->
                      let uu____2484 =
                        let uu____2491 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___163_2499 = wl  in
                           {
                             attempting = (uu___163_2499.attempting);
                             wl_deferred = (uu___163_2499.wl_deferred);
                             ctr = (uu___163_2499.ctr);
                             defer_ok = (uu___163_2499.defer_ok);
                             smt_ok = (uu___163_2499.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___163_2499.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2491
                          lg_ty false
                         in
                      (match uu____2484 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2511 =
                                   let uu____2516 =
                                     let uu____2517 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2517]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2516
                                    in
                                 uu____2511 FStar_Pervasives_Native.None loc
                              in
                           let uu____2538 =
                             let uu____2541 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2541;
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
                           (uu____2538, wl1))
  
let problem_using_guard :
  'Auu____2558 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2558 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2558 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2558 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2595 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2595;
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
  'Auu____2606 .
    worklist ->
      'Auu____2606 FStar_TypeChecker_Common.problem ->
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
        let uu____2656 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2656
        then
          let uu____2657 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2658 = prob_to_string env d  in
          let uu____2659 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2657 uu____2658 uu____2659 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2665 -> failwith "impossible"  in
           let uu____2666 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2678 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2679 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2678, uu____2679)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2683 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2684 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2683, uu____2684)
              in
           match uu____2666 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___132_2702  ->
            match uu___132_2702 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2714 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___133_2736  ->
           match uu___133_2736 with
           | UNIV uu____2739 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2746 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2746
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
        (fun uu___134_2770  ->
           match uu___134_2770 with
           | UNIV (u',t) ->
               let uu____2775 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2775
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2779 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2790 =
        let uu____2791 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2791
         in
      FStar_Syntax_Subst.compress uu____2790
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2802 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2802
  
let norm_arg :
  'Auu____2809 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2809) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2809)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2832 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2832, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2873  ->
              match uu____2873 with
              | (x,imp) ->
                  let uu____2884 =
                    let uu___164_2885 = x  in
                    let uu____2886 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___164_2885.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___164_2885.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2886
                    }  in
                  (uu____2884, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2907 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2907
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2911 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2911
        | uu____2914 -> u2  in
      let uu____2915 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2915
  
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
                (let uu____3029 = norm_refinement env t12  in
                 match uu____3029 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3044;
                     FStar_Syntax_Syntax.vars = uu____3045;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3071 =
                       let uu____3072 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3073 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3072 uu____3073
                        in
                     failwith uu____3071)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3087 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3087
          | FStar_Syntax_Syntax.Tm_uinst uu____3088 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3123 =
                   let uu____3124 = FStar_Syntax_Subst.compress t1'  in
                   uu____3124.FStar_Syntax_Syntax.n  in
                 match uu____3123 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3139 -> aux true t1'
                 | uu____3146 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3161 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3190 =
                   let uu____3191 = FStar_Syntax_Subst.compress t1'  in
                   uu____3191.FStar_Syntax_Syntax.n  in
                 match uu____3190 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3206 -> aux true t1'
                 | uu____3213 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3228 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3271 =
                   let uu____3272 = FStar_Syntax_Subst.compress t1'  in
                   uu____3272.FStar_Syntax_Syntax.n  in
                 match uu____3271 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3287 -> aux true t1'
                 | uu____3294 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3309 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3324 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3339 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3354 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3369 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3396 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3427 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3448 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3477 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3504 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3541 ->
              let uu____3548 =
                let uu____3549 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3550 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3549 uu____3550
                 in
              failwith uu____3548
          | FStar_Syntax_Syntax.Tm_ascribed uu____3563 ->
              let uu____3590 =
                let uu____3591 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3592 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3591 uu____3592
                 in
              failwith uu____3590
          | FStar_Syntax_Syntax.Tm_delayed uu____3605 ->
              let uu____3630 =
                let uu____3631 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3632 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3631 uu____3632
                 in
              failwith uu____3630
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3645 =
                let uu____3646 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3647 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3646 uu____3647
                 in
              failwith uu____3645
           in
        let uu____3660 = whnf env t1  in aux false uu____3660
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3691 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3691 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3722 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3722 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3758 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3758, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3769 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3769 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3794 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3794 with
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
  fun uu____3871  ->
    match uu____3871 with
    | (t_base,refopt) ->
        let uu____3904 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3904 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3944 =
      let uu____3947 =
        let uu____3950 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3973  ->
                  match uu____3973 with | (uu____3980,uu____3981,x) -> x))
           in
        FStar_List.append wl.attempting uu____3950  in
      FStar_List.map (wl_prob_to_string wl) uu____3947  in
    FStar_All.pipe_right uu____3944 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____3995 .
    ('Auu____3995,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4006  ->
    match uu____4006 with
    | (uu____4013,c,args) ->
        let uu____4016 = print_ctx_uvar c  in
        let uu____4017 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4016 uu____4017
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4023 = FStar_Syntax_Util.head_and_args t  in
    match uu____4023 with
    | (head1,_args) ->
        let uu____4060 =
          let uu____4061 = FStar_Syntax_Subst.compress head1  in
          uu____4061.FStar_Syntax_Syntax.n  in
        (match uu____4060 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4064 -> true
         | uu____4079 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4085 = FStar_Syntax_Util.head_and_args t  in
    match uu____4085 with
    | (head1,_args) ->
        let uu____4122 =
          let uu____4123 = FStar_Syntax_Subst.compress head1  in
          uu____4123.FStar_Syntax_Syntax.n  in
        (match uu____4122 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4127) -> u
         | uu____4148 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4171 = FStar_Syntax_Util.head_and_args t  in
      match uu____4171 with
      | (head1,args) ->
          let uu____4212 =
            let uu____4213 = FStar_Syntax_Subst.compress head1  in
            uu____4213.FStar_Syntax_Syntax.n  in
          (match uu____4212 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4221)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4264 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___135_4289  ->
                         match uu___135_4289 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4293 =
                               let uu____4294 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4294.FStar_Syntax_Syntax.n  in
                             (match uu____4293 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4298 -> false)
                         | uu____4299 -> true))
                  in
               (match uu____4264 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4321 =
                        FStar_List.collect
                          (fun uu___136_4327  ->
                             match uu___136_4327 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4331 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4331]
                             | uu____4332 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4321 FStar_List.rev  in
                    let uu____4341 =
                      let uu____4348 =
                        let uu____4355 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___137_4369  ->
                                  match uu___137_4369 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4373 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4373]
                                  | uu____4374 -> []))
                           in
                        FStar_All.pipe_right uu____4355 FStar_List.rev  in
                      let uu____4391 =
                        let uu____4394 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4394  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4348 uu____4391
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4341 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4423  ->
                                match uu____4423 with
                                | (x,i) ->
                                    let uu____4434 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4434, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4457  ->
                                match uu____4457 with
                                | (a,i) ->
                                    let uu____4468 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4468, i)) args_sol
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
           | uu____4484 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4504 =
          let uu____4517 =
            let uu____4518 = FStar_Syntax_Subst.compress k  in
            uu____4518.FStar_Syntax_Syntax.n  in
          match uu____4517 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4571 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4571)
              else
                (let uu____4585 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4585 with
                 | (ys',t1,uu____4608) ->
                     let uu____4613 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4613))
          | uu____4654 ->
              let uu____4655 =
                let uu____4666 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4666)  in
              ((ys, t), uu____4655)
           in
        match uu____4504 with
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
                 let uu____4715 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4715 c  in
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
               (let uu____4789 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4789
                then
                  let uu____4790 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4791 = print_ctx_uvar uv  in
                  let uu____4792 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4790 uu____4791 uu____4792
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
             let uu____4798 = p_guard_uvar prob  in
             match uu____4798 with
             | (xs,uv) ->
                 let fail1 uu____4810 =
                   let uu____4811 =
                     let uu____4812 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4813 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4812 uu____4813
                      in
                   failwith uu____4811  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____4863  ->
                           match uu____4863 with
                           | (a,i) ->
                               let uu____4876 =
                                 let uu____4877 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____4877.FStar_Syntax_Syntax.n  in
                               (match uu____4876 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____4895 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____4903 =
                     let uu____4904 = is_flex g  in
                     Prims.op_Negation uu____4904  in
                   if uu____4903
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____4908 = destruct_flex_t g wl  in
                      match uu____4908 with
                      | ((uu____4913,uv1,args),wl1) ->
                          ((let uu____4918 = args_as_binders args  in
                            assign_solution uu____4918 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___165_4920 = wl1  in
                   {
                     attempting = (uu___165_4920.attempting);
                     wl_deferred = (uu___165_4920.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___165_4920.defer_ok);
                     smt_ok = (uu___165_4920.smt_ok);
                     tcenv = (uu___165_4920.tcenv);
                     wl_implicits = (uu___165_4920.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4941 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4941
         then
           let uu____4942 = FStar_Util.string_of_int pid  in
           let uu____4943 =
             let uu____4944 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4944 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4942 uu____4943
         else ());
        commit sol;
        (let uu___166_4951 = wl  in
         {
           attempting = (uu___166_4951.attempting);
           wl_deferred = (uu___166_4951.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___166_4951.defer_ok);
           smt_ok = (uu___166_4951.smt_ok);
           tcenv = (uu___166_4951.tcenv);
           wl_implicits = (uu___166_4951.wl_implicits)
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
             | (uu____5013,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5039 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5039
              in
           (let uu____5045 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5045
            then
              let uu____5046 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5047 =
                let uu____5048 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5048 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5046 uu____5047
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
        let uu____5073 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5073 FStar_Util.set_elements  in
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
      let uu____5107 = occurs uk t  in
      match uu____5107 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5136 =
                 let uu____5137 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5138 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5137 uu____5138
                  in
               FStar_Pervasives_Native.Some uu____5136)
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
            let uu____5227 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5227 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5271 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5319  ->
             match uu____5319 with
             | (x,uu____5329) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5342 = FStar_List.last bs  in
      match uu____5342 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5360) ->
          let uu____5365 =
            FStar_Util.prefix_until
              (fun uu___138_5380  ->
                 match uu___138_5380 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5382 -> false) g
             in
          (match uu____5365 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5395,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5431 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5431 with
        | (pfx,uu____5441) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5453 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5453 with
             | (uu____5460,src',wl1) ->
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
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g  ->
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
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____5560 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5561 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5615  ->
                  fun uu____5616  ->
                    match (uu____5615, uu____5616) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5697 =
                          let uu____5698 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5698
                           in
                        if uu____5697
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5723 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5723
                           then
                             let uu____5736 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5736)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5561 with | (isect,uu____5773) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5802 'Auu____5803 .
    (FStar_Syntax_Syntax.bv,'Auu____5802) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5803) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5860  ->
              fun uu____5861  ->
                match (uu____5860, uu____5861) with
                | ((a,uu____5879),(b,uu____5881)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5896 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5896) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5926  ->
           match uu____5926 with
           | (y,uu____5932) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5943 'Auu____5944 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5943) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5944)
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
                   let uu____6053 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6053
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____6061 =
                        let uu____6064 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____6064 :: seen  in
                      aux uu____6061 args2)
               | uu____6065 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6095 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____6132 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6138 -> false
  
let string_of_option :
  'Auu____6145 .
    ('Auu____6145 -> Prims.string) ->
      'Auu____6145 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___139_6160  ->
      match uu___139_6160 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6166 = f x  in Prims.strcat "Some " uu____6166
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___140_6171  ->
    match uu___140_6171 with
    | MisMatch (d1,d2) ->
        let uu____6182 =
          let uu____6183 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6184 =
            let uu____6185 =
              let uu____6186 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6186 ")"  in
            Prims.strcat ") (" uu____6185  in
          Prims.strcat uu____6183 uu____6184  in
        Prims.strcat "MisMatch (" uu____6182
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___141_6191  ->
    match uu___141_6191 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____6206 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____6236 = m2 ()  in
          (match uu____6236 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____6251 -> HeadMatch)
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
          let uu____6265 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6265 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6276 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6299 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6308 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6336 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6336
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6337 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6338 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6339 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6354 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6367 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6391) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6397,uu____6398) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6440) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6461;
             FStar_Syntax_Syntax.index = uu____6462;
             FStar_Syntax_Syntax.sort = t2;_},uu____6464)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6471 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6472 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6473 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6486 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6493 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6511 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6511
  
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
            let uu____6538 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6538
            then FullMatch
            else
              (let uu____6540 =
                 let uu____6549 =
                   let uu____6552 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6552  in
                 let uu____6553 =
                   let uu____6556 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6556  in
                 (uu____6549, uu____6553)  in
               MisMatch uu____6540)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6562),FStar_Syntax_Syntax.Tm_uinst (g,uu____6564)) ->
            let uu____6573 = head_matches env f g  in
            FStar_All.pipe_right uu____6573 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6576 = FStar_Const.eq_const c d  in
            if uu____6576
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6583),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6585)) ->
            let uu____6626 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6626
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6633),FStar_Syntax_Syntax.Tm_refine (y,uu____6635)) ->
            let uu____6644 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6644 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6646),uu____6647) ->
            let uu____6652 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6652 head_match
        | (uu____6653,FStar_Syntax_Syntax.Tm_refine (x,uu____6655)) ->
            let uu____6660 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6660 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6661,FStar_Syntax_Syntax.Tm_type
           uu____6662) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6663,FStar_Syntax_Syntax.Tm_arrow uu____6664) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6690),FStar_Syntax_Syntax.Tm_app (head',uu____6692))
            ->
            let uu____6733 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6733 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6735),uu____6736) ->
            let uu____6757 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6757 head_match
        | (uu____6758,FStar_Syntax_Syntax.Tm_app (head1,uu____6760)) ->
            let uu____6781 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6781 head_match
        | uu____6782 ->
            let uu____6787 =
              let uu____6796 = delta_depth_of_term env t11  in
              let uu____6799 = delta_depth_of_term env t21  in
              (uu____6796, uu____6799)  in
            MisMatch uu____6787
  
let head_matches_delta :
  'Auu____6816 .
    FStar_TypeChecker_Env.env ->
      'Auu____6816 ->
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
            let uu____6863 = FStar_Syntax_Util.head_and_args t  in
            match uu____6863 with
            | (head1,uu____6881) ->
                let uu____6902 =
                  let uu____6903 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6903.FStar_Syntax_Syntax.n  in
                (match uu____6902 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6909 =
                       let uu____6910 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6910 FStar_Option.isSome
                        in
                     if uu____6909
                     then
                       let uu____6929 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6929
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6933 -> FStar_Pervasives_Native.None)
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
              let uu____7066 =
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
              match uu____7066 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____7111 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____7111 with
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
                 uu____7143),uu____7144)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7162 =
                     let uu____7171 = maybe_inline t11  in
                     let uu____7174 = maybe_inline t21  in
                     (uu____7171, uu____7174)  in
                   match uu____7162 with
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
                (uu____7211,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____7212))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7230 =
                     let uu____7239 = maybe_inline t11  in
                     let uu____7242 = maybe_inline t21  in
                     (uu____7239, uu____7242)  in
                   match uu____7230 with
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
            | MisMatch uu____7291 -> fail1 r
            | uu____7300 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7313 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7313
           then
             let uu____7314 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7315 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7316 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7323 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7341 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7341
                    (fun uu____7375  ->
                       match uu____7375 with
                       | (t11,t21) ->
                           let uu____7382 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7383 =
                             let uu____7384 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7384  in
                           Prims.strcat uu____7382 uu____7383))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____7314
               uu____7315 uu____7316 uu____7323
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7396 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7396 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___142_7409  ->
    match uu___142_7409 with
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
      let uu___167_7446 = p  in
      let uu____7449 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7450 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___167_7446.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7449;
        FStar_TypeChecker_Common.relation =
          (uu___167_7446.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7450;
        FStar_TypeChecker_Common.element =
          (uu___167_7446.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___167_7446.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___167_7446.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___167_7446.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___167_7446.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___167_7446.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7464 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7464
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____7469 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7491 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7491 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7499 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7499 with
           | (lh,lhs_args) ->
               let uu____7540 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7540 with
                | (rh,rhs_args) ->
                    let uu____7581 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7594,FStar_Syntax_Syntax.Tm_uvar uu____7595)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7676 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7699,uu____7700)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7718 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7718.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7718.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7718.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7718.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7718.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7718.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7718.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7718.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7718.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7721,FStar_Syntax_Syntax.Tm_uvar uu____7722)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7740 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7740.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7740.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7740.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7740.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7740.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7740.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7740.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7740.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7740.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7743,FStar_Syntax_Syntax.Tm_arrow uu____7744)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7774 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7774.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7774.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7774.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7774.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7774.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7774.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7774.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7774.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7774.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7777,FStar_Syntax_Syntax.Tm_type uu____7778)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7796 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7796.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7796.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7796.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7796.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7796.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7796.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7796.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7796.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7796.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7799,FStar_Syntax_Syntax.Tm_uvar uu____7800)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7818 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7818.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7818.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7818.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7818.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7818.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7818.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7818.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7818.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7818.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7821,FStar_Syntax_Syntax.Tm_uvar uu____7822)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7839,uu____7840)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7857,FStar_Syntax_Syntax.Tm_uvar uu____7858)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7875,uu____7876) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7581 with
                     | (rank,tp1) ->
                         let uu____7889 =
                           FStar_All.pipe_right
                             (let uu___170_7893 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___170_7893.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___170_7893.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___170_7893.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___170_7893.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___170_7893.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___170_7893.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___170_7893.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___170_7893.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___170_7893.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7889))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7899 =
            FStar_All.pipe_right
              (let uu___171_7903 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___171_7903.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___171_7903.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___171_7903.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___171_7903.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___171_7903.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___171_7903.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___171_7903.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___171_7903.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___171_7903.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7899)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____7964 probs =
      match uu____7964 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8045 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8066 = rank wl.tcenv hd1  in
               (match uu____8066 with
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
                      (let uu____8125 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8129 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8129)
                          in
                       if uu____8125
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
          let uu____8197 = FStar_Syntax_Util.head_and_args t  in
          match uu____8197 with
          | (hd1,uu____8213) ->
              let uu____8234 =
                let uu____8235 = FStar_Syntax_Subst.compress hd1  in
                uu____8235.FStar_Syntax_Syntax.n  in
              (match uu____8234 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8239) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8273  ->
                           match uu____8273 with
                           | (y,uu____8279) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8293  ->
                                       match uu____8293 with
                                       | (x,uu____8299) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8300 -> false)
           in
        let uu____8301 = rank tcenv p  in
        match uu____8301 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8308 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8335 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8349 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8363 -> false
  
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
                        let uu____8415 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8415 with
                        | (k,uu____8421) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8431 -> false)))
            | uu____8432 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8484 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8490 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8490 = (Prims.parse_int "0")))
                           in
                        if uu____8484 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8506 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8512 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8512 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8506)
               in
            let uu____8513 = filter1 u12  in
            let uu____8516 = filter1 u22  in (uu____8513, uu____8516)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8545 = filter_out_common_univs us1 us2  in
                (match uu____8545 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8604 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8604 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8607 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8617 =
                          let uu____8618 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8619 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8618
                            uu____8619
                           in
                        UFailed uu____8617))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8643 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8643 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8669 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8669 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8672 ->
                let uu____8677 =
                  let uu____8678 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8679 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8678
                    uu____8679 msg
                   in
                UFailed uu____8677
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8680,uu____8681) ->
              let uu____8682 =
                let uu____8683 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8684 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8683 uu____8684
                 in
              failwith uu____8682
          | (FStar_Syntax_Syntax.U_unknown ,uu____8685) ->
              let uu____8686 =
                let uu____8687 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8688 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8687 uu____8688
                 in
              failwith uu____8686
          | (uu____8689,FStar_Syntax_Syntax.U_bvar uu____8690) ->
              let uu____8691 =
                let uu____8692 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8693 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8692 uu____8693
                 in
              failwith uu____8691
          | (uu____8694,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8695 =
                let uu____8696 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8697 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8696 uu____8697
                 in
              failwith uu____8695
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8721 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8721
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8735 = occurs_univ v1 u3  in
              if uu____8735
              then
                let uu____8736 =
                  let uu____8737 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8738 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8737 uu____8738
                   in
                try_umax_components u11 u21 uu____8736
              else
                (let uu____8740 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8740)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8752 = occurs_univ v1 u3  in
              if uu____8752
              then
                let uu____8753 =
                  let uu____8754 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8755 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8754 uu____8755
                   in
                try_umax_components u11 u21 uu____8753
              else
                (let uu____8757 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8757)
          | (FStar_Syntax_Syntax.U_max uu____8758,uu____8759) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8765 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8765
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8767,FStar_Syntax_Syntax.U_max uu____8768) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8774 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8774
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8776,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8777,FStar_Syntax_Syntax.U_name
             uu____8778) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8779) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8780) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8781,FStar_Syntax_Syntax.U_succ
             uu____8782) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8783,FStar_Syntax_Syntax.U_zero
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
      let uu____8883 = bc1  in
      match uu____8883 with
      | (bs1,mk_cod1) ->
          let uu____8927 = bc2  in
          (match uu____8927 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9038 = aux xs ys  in
                     (match uu____9038 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9121 =
                       let uu____9128 = mk_cod1 xs  in ([], uu____9128)  in
                     let uu____9131 =
                       let uu____9138 = mk_cod2 ys  in ([], uu____9138)  in
                     (uu____9121, uu____9131)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____9161 'Auu____9162 'Auu____9163 .
    ('Auu____9161,'Auu____9162,'Auu____9163 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___143_9176  ->
    match uu___143_9176 with
    | (uu____9185,uu____9186,[]) -> true
    | uu____9189 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9220 = f  in
      match uu____9220 with
      | (uu____9227,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9228;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9229;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9232;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9233;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9234;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9286  ->
                 match uu____9286 with
                 | (y,uu____9292) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9414 =
                  let uu____9427 =
                    let uu____9430 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9430  in
                  ((FStar_List.rev pat_binders), uu____9427)  in
                FStar_Pervasives_Native.Some uu____9414
            | (uu____9457,[]) ->
                let uu____9480 =
                  let uu____9493 =
                    let uu____9496 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9496  in
                  ((FStar_List.rev pat_binders), uu____9493)  in
                FStar_Pervasives_Native.Some uu____9480
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9561 =
                  let uu____9562 = FStar_Syntax_Subst.compress a  in
                  uu____9562.FStar_Syntax_Syntax.n  in
                (match uu____9561 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9580 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9580
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___172_9601 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___172_9601.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___172_9601.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9605 =
                            let uu____9606 =
                              let uu____9613 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9613)  in
                            FStar_Syntax_Syntax.NT uu____9606  in
                          [uu____9605]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___173_9625 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___173_9625.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___173_9625.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9626 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9654 =
                  let uu____9667 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9667  in
                (match uu____9654 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9730 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9757 ->
               let uu____9758 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9758 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10034 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10034
       then
         let uu____10035 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10035
       else ());
      (let uu____10037 = next_prob probs  in
       match uu____10037 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___174_10064 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___174_10064.wl_deferred);
               ctr = (uu___174_10064.ctr);
               defer_ok = (uu___174_10064.defer_ok);
               smt_ok = (uu___174_10064.smt_ok);
               tcenv = (uu___174_10064.tcenv);
               wl_implicits = (uu___174_10064.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10071 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10071
                then
                  let uu____10072 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10072
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
                          (let uu___175_10077 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___175_10077.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___175_10077.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___175_10077.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___175_10077.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___175_10077.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___175_10077.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___175_10077.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___175_10077.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___175_10077.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10099 ->
                let uu____10108 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10167  ->
                          match uu____10167 with
                          | (c,uu____10175,uu____10176) -> c < probs.ctr))
                   in
                (match uu____10108 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10217 =
                            let uu____10222 =
                              FStar_List.map
                                (fun uu____10237  ->
                                   match uu____10237 with
                                   | (uu____10248,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10222, (probs.wl_implicits))  in
                          Success uu____10217
                      | uu____10251 ->
                          let uu____10260 =
                            let uu___176_10261 = probs  in
                            let uu____10262 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10281  ->
                                      match uu____10281 with
                                      | (uu____10288,uu____10289,y) -> y))
                               in
                            {
                              attempting = uu____10262;
                              wl_deferred = rest;
                              ctr = (uu___176_10261.ctr);
                              defer_ok = (uu___176_10261.defer_ok);
                              smt_ok = (uu___176_10261.smt_ok);
                              tcenv = (uu___176_10261.tcenv);
                              wl_implicits = (uu___176_10261.wl_implicits)
                            }  in
                          solve env uu____10260))))

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
            let uu____10296 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10296 with
            | USolved wl1 ->
                let uu____10298 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10298
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
                  let uu____10350 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10350 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10353 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10365;
                  FStar_Syntax_Syntax.vars = uu____10366;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10369;
                  FStar_Syntax_Syntax.vars = uu____10370;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10382,uu____10383) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10390,FStar_Syntax_Syntax.Tm_uinst uu____10391) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10398 -> USolved wl

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
            ((let uu____10408 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10408
              then
                let uu____10409 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10409 msg
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
              let uu____10494 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10494 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10546 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10546
               then
                 let uu____10547 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10548 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10547
                   uu____10548
               else ());
              (let uu____10550 = head_matches_delta env1 () t1 t2  in
               match uu____10550 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____10595 ->
                        let uu____10604 = eq_prob t1 t2 wl2  in
                        (match uu____10604 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____10651 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10666 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10667 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10666, uu____10667)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10672 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10673 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10672, uu____10673)
                           in
                        (match uu____10651 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10704 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10704 with
                               | (t1_hd,t1_args) ->
                                   let uu____10743 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10743 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____10797 =
                                             let uu____10804 =
                                               let uu____10813 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____10813 :: t1_args  in
                                             let uu____10826 =
                                               let uu____10833 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____10833 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____10874  ->
                                                  fun uu____10875  ->
                                                    fun uu____10876  ->
                                                      match (uu____10874,
                                                              uu____10875,
                                                              uu____10876)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____10918),
                                                         (a2,uu____10920)) ->
                                                          let uu____10945 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____10945
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____10804
                                               uu____10826
                                              in
                                           match uu____10797 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___177_10971 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___177_10971.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___177_10971.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10989 =
                                                 solve env1 wl'  in
                                               (match uu____10989 with
                                                | Success (uu____10992,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___178_10996 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___178_10996.attempting);
                                                           wl_deferred =
                                                             (uu___178_10996.wl_deferred);
                                                           ctr =
                                                             (uu___178_10996.ctr);
                                                           defer_ok =
                                                             (uu___178_10996.defer_ok);
                                                           smt_ok =
                                                             (uu___178_10996.smt_ok);
                                                           tcenv =
                                                             (uu___178_10996.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11007 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11039 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11039 with
                               | (t1_base,p1_opt) ->
                                   let uu____11080 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11080 with
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
                                              let uu____11211 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____11211
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
                                              let uu____11241 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11241
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
                                              let uu____11271 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11271
                                          | uu____11274 -> t_base  in
                                        let uu____11291 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11291 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11305 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11305, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11312 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11312 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11353 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11353 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11394 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11394
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
                             let uu____11418 = combine t11 t21 wl2  in
                             (match uu____11418 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11451 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11451
                                    then
                                      let uu____11452 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11452
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11491 ts1 =
              match uu____11491 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11554 = pairwise out t wl2  in
                       (match uu____11554 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11590 =
              let uu____11601 = FStar_List.hd ts  in (uu____11601, [], wl1)
               in
            let uu____11610 = FStar_List.tl ts  in
            aux uu____11590 uu____11610  in
          let uu____11617 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11617 with
          | (this_flex,this_rigid) ->
              let uu____11629 =
                let uu____11630 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11630.FStar_Syntax_Syntax.n  in
              (match uu____11629 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11651 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11651
                   then
                     let uu____11652 = destruct_flex_t this_flex wl  in
                     (match uu____11652 with
                      | (flex,wl1) ->
                          let uu____11659 = quasi_pattern env flex  in
                          (match uu____11659 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11677 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11677
                                 then
                                   let uu____11678 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11678
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
                             ((let uu___179_11683 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___179_11683.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___179_11683.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___179_11683.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___179_11683.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___179_11683.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___179_11683.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___179_11683.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___179_11683.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___179_11683.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11684 ->
                   ((let uu____11686 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11686
                     then
                       let uu____11687 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11687
                     else ());
                    (let uu____11689 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11689 with
                     | (u,_args) ->
                         let uu____11726 =
                           let uu____11727 = FStar_Syntax_Subst.compress u
                              in
                           uu____11727.FStar_Syntax_Syntax.n  in
                         (match uu____11726 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____11758 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____11758 with
                                | (u',uu____11774) ->
                                    let uu____11795 =
                                      let uu____11796 = whnf env u'  in
                                      uu____11796.FStar_Syntax_Syntax.n  in
                                    (match uu____11795 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____11821 -> false)
                                 in
                              let uu____11822 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___144_11845  ->
                                        match uu___144_11845 with
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
                                             | uu____11854 -> false)
                                        | uu____11857 -> false))
                                 in
                              (match uu____11822 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____11871 = whnf env this_rigid
                                        in
                                     let uu____11872 =
                                       FStar_List.collect
                                         (fun uu___145_11878  ->
                                            match uu___145_11878 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____11884 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____11884]
                                            | uu____11886 -> []) bounds_probs
                                        in
                                     uu____11871 :: uu____11872  in
                                   let uu____11887 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____11887 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____11918 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____11933 =
                                              let uu____11934 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____11934.FStar_Syntax_Syntax.n
                                               in
                                            match uu____11933 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____11946 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____11946)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____11955 -> bound  in
                                          let uu____11956 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____11956)  in
                                        (match uu____11918 with
                                         | (bound_typ,(eq_prob,wl2)) ->
                                             ((let uu____11984 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____11984
                                               then
                                                 let wl' =
                                                   let uu___180_11986 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___180_11986.wl_deferred);
                                                     ctr =
                                                       (uu___180_11986.ctr);
                                                     defer_ok =
                                                       (uu___180_11986.defer_ok);
                                                     smt_ok =
                                                       (uu___180_11986.smt_ok);
                                                     tcenv =
                                                       (uu___180_11986.tcenv);
                                                     wl_implicits =
                                                       (uu___180_11986.wl_implicits)
                                                   }  in
                                                 let uu____11987 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____11987
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11990 =
                                                 solve_t env eq_prob
                                                   (let uu___181_11992 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___181_11992.wl_deferred);
                                                      ctr =
                                                        (uu___181_11992.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___181_11992.smt_ok);
                                                      tcenv =
                                                        (uu___181_11992.tcenv);
                                                      wl_implicits =
                                                        (uu___181_11992.wl_implicits)
                                                    })
                                                  in
                                               match uu____11990 with
                                               | Success uu____11993 ->
                                                   let wl3 =
                                                     let uu___182_11999 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___182_11999.wl_deferred);
                                                       ctr =
                                                         (uu___182_11999.ctr);
                                                       defer_ok =
                                                         (uu___182_11999.defer_ok);
                                                       smt_ok =
                                                         (uu___182_11999.smt_ok);
                                                       tcenv =
                                                         (uu___182_11999.tcenv);
                                                       wl_implicits =
                                                         (uu___182_11999.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____12003 =
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
                                                    (let uu____12015 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12015
                                                     then
                                                       let uu____12016 =
                                                         let uu____12017 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12017
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12016
                                                     else ());
                                                    (let uu____12023 =
                                                       let uu____12038 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12038)
                                                        in
                                                     match uu____12023 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12060))
                                                         ->
                                                         let uu____12085 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12085
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
                                                         let uu____12124 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12124
                                                          with
                                                          | (eq_prob1,wl3) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl3 tp x
                                                                  phi
                                                                 in
                                                              let wl4 =
                                                                let uu____12141
                                                                  =
                                                                  let uu____12146
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12146
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12141
                                                                  [] wl3
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl4))
                                                     | uu____12151 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12166 when flip ->
                              let uu____12167 =
                                let uu____12168 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12169 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12168 uu____12169
                                 in
                              failwith uu____12167
                          | uu____12170 ->
                              let uu____12171 =
                                let uu____12172 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12173 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12172 uu____12173
                                 in
                              failwith uu____12171))))

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
                      (fun uu____12201  ->
                         match uu____12201 with
                         | (x,i) ->
                             let uu____12212 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12212, i)) bs_lhs
                     in
                  let uu____12213 = lhs  in
                  match uu____12213 with
                  | (uu____12214,u_lhs,uu____12216) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12329 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12339 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12339, univ)
                             in
                          match uu____12329 with
                          | (k,univ) ->
                              let uu____12352 =
                                let uu____12359 =
                                  let uu____12362 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12362
                                   in
                                copy_uvar u_lhs uu____12359 wl2  in
                              (match uu____12352 with
                               | (uu____12375,u,wl3) ->
                                   let uu____12378 =
                                     let uu____12381 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12381
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12378, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12417 =
                              let uu____12430 =
                                let uu____12439 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12439 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12485  ->
                                   fun uu____12486  ->
                                     match (uu____12485, uu____12486) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12577 =
                                           let uu____12584 =
                                             let uu____12587 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12587
                                              in
                                           copy_uvar u_lhs uu____12584 wl2
                                            in
                                         (match uu____12577 with
                                          | (uu____12610,t_a,wl3) ->
                                              let uu____12613 =
                                                let uu____12620 =
                                                  let uu____12623 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12623
                                                   in
                                                copy_uvar u_lhs uu____12620
                                                  wl3
                                                 in
                                              (match uu____12613 with
                                               | (uu____12638,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12430
                                ([], wl1)
                               in
                            (match uu____12417 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___183_12699 = ct  in
                                   let uu____12700 =
                                     let uu____12703 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12703
                                      in
                                   let uu____12718 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___183_12699.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___183_12699.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12700;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12718;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___183_12699.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___184_12736 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___184_12736.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___184_12736.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12739 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12739 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12793 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12793 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12810 =
                                          let uu____12815 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12815)  in
                                        TERM uu____12810  in
                                      let uu____12816 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12816 with
                                       | (sub_prob,wl3) ->
                                           let uu____12827 =
                                             let uu____12828 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12828
                                              in
                                           solve env uu____12827))
                             | (x,imp)::formals2 ->
                                 let uu____12842 =
                                   let uu____12849 =
                                     let uu____12852 =
                                       let uu____12855 =
                                         let uu____12856 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____12856
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____12855
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____12852
                                      in
                                   copy_uvar u_lhs uu____12849 wl1  in
                                 (match uu____12842 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____12880 =
                                          let uu____12883 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12883
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12880 t_y
                                         in
                                      let uu____12884 =
                                        let uu____12887 =
                                          let uu____12890 =
                                            let uu____12891 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12891, imp)  in
                                          [uu____12890]  in
                                        FStar_List.append bs_terms
                                          uu____12887
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12884 formals2 wl2)
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
              (let uu____12933 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12933
               then
                 let uu____12934 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12935 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12934 (rel_to_string (p_rel orig)) uu____12935
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13040 = rhs wl1 scope env1 subst1  in
                     (match uu____13040 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13060 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13060
                            then
                              let uu____13061 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13061
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___185_13115 = hd1  in
                       let uu____13116 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___185_13115.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___185_13115.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13116
                       }  in
                     let hd21 =
                       let uu___186_13120 = hd2  in
                       let uu____13121 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___186_13120.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___186_13120.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13121
                       }  in
                     let uu____13124 =
                       let uu____13129 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13129
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13124 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13148 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13148
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13152 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13152 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13207 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13207
                                  in
                               ((let uu____13219 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13219
                                 then
                                   let uu____13220 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13221 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13220
                                     uu____13221
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13248 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13277 = aux wl [] env [] bs1 bs2  in
               match uu____13277 with
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
        (let uu____13328 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13328 wl)

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
              let uu____13342 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13342 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13372 = lhs1  in
              match uu____13372 with
              | (uu____13375,ctx_u,uu____13377) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13383 ->
                        let uu____13384 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13384 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13431 = quasi_pattern env1 lhs1  in
              match uu____13431 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13461) ->
                  let uu____13466 = lhs1  in
                  (match uu____13466 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13480 = occurs_check ctx_u rhs1  in
                       (match uu____13480 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13522 =
                                let uu____13529 =
                                  let uu____13530 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13530
                                   in
                                FStar_Util.Inl uu____13529  in
                              (uu____13522, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13550 =
                                 let uu____13551 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13551  in
                               if uu____13550
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13571 =
                                    let uu____13578 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13578  in
                                  let uu____13583 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13571, uu____13583)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13645  ->
                     match uu____13645 with
                     | (x,i) ->
                         let uu____13656 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13656, i)) bs_lhs
                 in
              let uu____13657 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13657 with
              | (rhs_hd,args) ->
                  let uu____13694 = FStar_Util.prefix args  in
                  (match uu____13694 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13752 = lhs1  in
                       (match uu____13752 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13756 =
                              let uu____13767 =
                                let uu____13774 =
                                  let uu____13777 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13777
                                   in
                                copy_uvar u_lhs uu____13774 wl1  in
                              match uu____13767 with
                              | (uu____13798,t_last_arg,wl2) ->
                                  let uu____13801 =
                                    let uu____13808 =
                                      let uu____13811 =
                                        let uu____13818 =
                                          let uu____13825 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____13825]  in
                                        FStar_List.append bs_lhs uu____13818
                                         in
                                      let uu____13842 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____13811
                                        uu____13842
                                       in
                                    copy_uvar u_lhs uu____13808 wl2  in
                                  (match uu____13801 with
                                   | (uu____13855,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13861 =
                                         let uu____13868 =
                                           let uu____13871 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____13871
                                            in
                                         copy_uvar u_lhs uu____13868 wl3  in
                                       (match uu____13861 with
                                        | (uu____13884,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13756 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13908 =
                                     let uu____13909 =
                                       let uu____13914 =
                                         let uu____13915 =
                                           let uu____13918 =
                                             let uu____13923 =
                                               let uu____13924 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13924]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13923
                                              in
                                           uu____13918
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13915
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13914)  in
                                     TERM uu____13909  in
                                   [uu____13908]  in
                                 let uu____13945 =
                                   let uu____13952 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____13952 with
                                   | (p1,wl3) ->
                                       let uu____13969 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____13969 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13945 with
                                  | (sub_probs,wl3) ->
                                      let uu____13996 =
                                        let uu____13997 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____13997  in
                                      solve env1 uu____13996))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14030 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14030 with
                | (uu____14045,args) ->
                    (match args with | [] -> false | uu____14073 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14088 =
                  let uu____14089 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14089.FStar_Syntax_Syntax.n  in
                match uu____14088 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14092 -> true
                | uu____14105 -> false  in
              let uu____14106 = quasi_pattern env1 lhs1  in
              match uu____14106 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14117 =
                    let uu____14118 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14118
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14117
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14125 = is_app rhs1  in
                  if uu____14125
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14127 = is_arrow rhs1  in
                     if uu____14127
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14129 =
                          let uu____14130 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14130
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14129))
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
                let uu____14133 = lhs  in
                (match uu____14133 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14137 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14137 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14152 =
                              let uu____14155 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14155
                               in
                            FStar_All.pipe_right uu____14152
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14170 = occurs_check ctx_uv rhs1  in
                          (match uu____14170 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14192 =
                                   let uu____14193 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14193
                                    in
                                 giveup_or_defer env orig wl uu____14192
                               else
                                 (let uu____14195 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14195
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14200 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14200
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14202 =
                                         let uu____14203 =
                                           names_to_string1 fvs2  in
                                         let uu____14204 =
                                           names_to_string1 fvs1  in
                                         let uu____14205 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14203 uu____14204
                                           uu____14205
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14202)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14211 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14215 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14215 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14238 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14238
                             | (FStar_Util.Inl msg,uu____14240) ->
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
                  (let uu____14269 =
                     let uu____14286 = quasi_pattern env lhs  in
                     let uu____14293 = quasi_pattern env rhs  in
                     (uu____14286, uu____14293)  in
                   match uu____14269 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14336 = lhs  in
                       (match uu____14336 with
                        | ({ FStar_Syntax_Syntax.n = uu____14337;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14339;_},u_lhs,uu____14341)
                            ->
                            let uu____14344 = rhs  in
                            (match uu____14344 with
                             | (uu____14345,u_rhs,uu____14347) ->
                                 let uu____14348 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14348
                                 then
                                   let uu____14349 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14349
                                 else
                                   (let uu____14351 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14351 with
                                    | (sub_prob,wl1) ->
                                        let uu____14362 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14362 with
                                         | (ctx_w,(ctx_l,ctx_r)) ->
                                             let gamma_w =
                                               gamma_until
                                                 u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                                 ctx_w
                                                in
                                             let zs =
                                               intersect_binders gamma_w
                                                 (FStar_List.append ctx_l
                                                    binders_lhs)
                                                 (FStar_List.append ctx_r
                                                    binders_rhs)
                                                in
                                             let uu____14390 =
                                               let uu____14397 =
                                                 let uu____14400 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14400
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi:"
                                                    (Prims.strcat "\tlhs="
                                                       (Prims.strcat
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                          (Prims.strcat
                                                             "\trhs="
                                                             u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                                 wl1 range gamma_w ctx_w
                                                 uu____14397
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____14390 with
                                              | (uu____14403,w,wl2) ->
                                                  let w_app =
                                                    let uu____14409 =
                                                      let uu____14414 =
                                                        FStar_List.map
                                                          (fun uu____14423 
                                                             ->
                                                             match uu____14423
                                                             with
                                                             | (z,uu____14429)
                                                                 ->
                                                                 let uu____14430
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14430)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14414
                                                       in
                                                    uu____14409
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14434 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14434
                                                    then
                                                      let uu____14435 =
                                                        let uu____14438 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14439 =
                                                          let uu____14442 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14443 =
                                                            let uu____14446 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14447 =
                                                              let uu____14450
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14455
                                                                =
                                                                let uu____14458
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14463
                                                                  =
                                                                  let uu____14466
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14466]
                                                                   in
                                                                uu____14458
                                                                  ::
                                                                  uu____14463
                                                                 in
                                                              uu____14450 ::
                                                                uu____14455
                                                               in
                                                            uu____14446 ::
                                                              uu____14447
                                                             in
                                                          uu____14442 ::
                                                            uu____14443
                                                           in
                                                        uu____14438 ::
                                                          uu____14439
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14435
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14472 =
                                                          let uu____14477 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14477)
                                                           in
                                                        TERM uu____14472  in
                                                      let uu____14478 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14478
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14483 =
                                                             let uu____14488
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
                                                               uu____14488)
                                                              in
                                                           TERM uu____14483
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14489 =
                                                      let uu____14490 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14490
                                                       in
                                                    solve env uu____14489)))))))
                   | uu____14491 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____14559 = head_matches_delta env1 wl1 t1 t2  in
           match uu____14559 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____14590,uu____14591) ->
                    let rec may_relate head3 =
                      let uu____14618 =
                        let uu____14619 = FStar_Syntax_Subst.compress head3
                           in
                        uu____14619.FStar_Syntax_Syntax.n  in
                      match uu____14618 with
                      | FStar_Syntax_Syntax.Tm_name uu____14622 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____14623 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14646;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____14647;
                            FStar_Syntax_Syntax.fv_qual = uu____14648;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14651;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____14652;
                            FStar_Syntax_Syntax.fv_qual = uu____14653;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____14657,uu____14658) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____14700) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____14706) ->
                          may_relate t
                      | uu____14711 -> false  in
                    let uu____14712 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____14712
                    then
                      let uu____14713 =
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
                                 let uu____14745 =
                                   let uu____14746 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____14746 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____14745
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____14751 = has_type_guard t1 t2  in
                             (uu____14751, wl1)
                           else
                             (let uu____14757 = has_type_guard t2 t1  in
                              (uu____14757, wl1)))
                         in
                      (match uu____14713 with
                       | (guard,wl2) ->
                           let uu____14764 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____14764)
                    else
                      (let uu____14766 =
                         let uu____14767 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14768 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____14767 uu____14768
                          in
                       giveup env1 uu____14766 orig)
                | (uu____14769,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___187_14783 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___187_14783.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___187_14783.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___187_14783.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___187_14783.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___187_14783.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___187_14783.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___187_14783.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___187_14783.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____14784,FStar_Pervasives_Native.None ) ->
                    ((let uu____14796 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14796
                      then
                        let uu____14797 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____14798 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____14799 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____14800 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____14797 uu____14798 uu____14799 uu____14800
                      else ());
                     (let uu____14802 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____14802 with
                      | (head11,args1) ->
                          let uu____14839 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____14839 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____14893 =
                                   let uu____14894 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____14895 = args_to_string args1  in
                                   let uu____14896 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____14897 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____14894 uu____14895 uu____14896
                                     uu____14897
                                    in
                                 giveup env1 uu____14893 orig
                               else
                                 (let uu____14899 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____14906 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____14906 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____14899
                                  then
                                    let uu____14907 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____14907 with
                                    | USolved wl2 ->
                                        let uu____14909 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____14909
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____14913 =
                                       base_and_refinement env1 t1  in
                                     match uu____14913 with
                                     | (base1,refinement1) ->
                                         let uu____14938 =
                                           base_and_refinement env1 t2  in
                                         (match uu____14938 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____14995 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____14995 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____14999 =
                                                          FStar_List.fold_right2
                                                            (fun uu____15032 
                                                               ->
                                                               fun
                                                                 uu____15033 
                                                                 ->
                                                                 fun
                                                                   uu____15034
                                                                    ->
                                                                   match 
                                                                    (uu____15032,
                                                                    uu____15033,
                                                                    uu____15034)
                                                                   with
                                                                   | 
                                                                   ((a,uu____15070),
                                                                    (a',uu____15072),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____15093
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____15093
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
                                                        (match uu____14999
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____15121
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____15121
                                                               then
                                                                 let uu____15122
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____15122
                                                               else ());
                                                              (let formula =
                                                                 let uu____15127
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____15127
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
                                               | uu____15135 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___188_15175 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___188_15175.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15178 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15178
          then
            let uu____15179 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15179
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15184 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15184
              then
                let uu____15185 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15186 =
                  let uu____15187 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15188 =
                    let uu____15189 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15189  in
                  Prims.strcat uu____15187 uu____15188  in
                let uu____15190 =
                  let uu____15191 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15192 =
                    let uu____15193 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15193  in
                  Prims.strcat uu____15191 uu____15192  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15185
                  uu____15186 uu____15190
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15196,uu____15197) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15222,FStar_Syntax_Syntax.Tm_delayed uu____15223) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15248,uu____15249) ->
                  let uu____15276 =
                    let uu___189_15277 = problem  in
                    let uu____15278 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___189_15277.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15278;
                      FStar_TypeChecker_Common.relation =
                        (uu___189_15277.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___189_15277.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___189_15277.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___189_15277.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___189_15277.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___189_15277.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___189_15277.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___189_15277.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15276 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15279,uu____15280) ->
                  let uu____15287 =
                    let uu___190_15288 = problem  in
                    let uu____15289 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___190_15288.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15289;
                      FStar_TypeChecker_Common.relation =
                        (uu___190_15288.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___190_15288.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___190_15288.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___190_15288.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___190_15288.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___190_15288.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___190_15288.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___190_15288.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15287 wl
              | (uu____15290,FStar_Syntax_Syntax.Tm_ascribed uu____15291) ->
                  let uu____15318 =
                    let uu___191_15319 = problem  in
                    let uu____15320 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___191_15319.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___191_15319.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___191_15319.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15320;
                      FStar_TypeChecker_Common.element =
                        (uu___191_15319.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___191_15319.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___191_15319.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___191_15319.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___191_15319.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___191_15319.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15318 wl
              | (uu____15321,FStar_Syntax_Syntax.Tm_meta uu____15322) ->
                  let uu____15329 =
                    let uu___192_15330 = problem  in
                    let uu____15331 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___192_15330.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___192_15330.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___192_15330.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15331;
                      FStar_TypeChecker_Common.element =
                        (uu___192_15330.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___192_15330.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___192_15330.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___192_15330.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___192_15330.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___192_15330.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15329 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15333),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15335)) ->
                  let uu____15344 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15344
              | (FStar_Syntax_Syntax.Tm_bvar uu____15345,uu____15346) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15347,FStar_Syntax_Syntax.Tm_bvar uu____15348) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___146_15407 =
                    match uu___146_15407 with
                    | [] -> c
                    | bs ->
                        let uu____15429 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15429
                     in
                  let uu____15438 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15438 with
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
                                    let uu____15561 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15561
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
                  let mk_t t l uu___147_15636 =
                    match uu___147_15636 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15670 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15670 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____15789 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____15790 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____15789
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____15790 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____15791,uu____15792) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15819 -> true
                    | uu____15836 -> false  in
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
                      (let uu____15877 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___193_15885 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___193_15885.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___193_15885.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___193_15885.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___193_15885.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___193_15885.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___193_15885.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___193_15885.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___193_15885.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___193_15885.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___193_15885.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___193_15885.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___193_15885.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___193_15885.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___193_15885.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___193_15885.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___193_15885.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___193_15885.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___193_15885.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___193_15885.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___193_15885.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___193_15885.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___193_15885.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___193_15885.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___193_15885.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___193_15885.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___193_15885.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___193_15885.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___193_15885.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___193_15885.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___193_15885.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___193_15885.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___193_15885.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___193_15885.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___193_15885.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___193_15885.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15877 with
                       | (uu____15888,ty,uu____15890) ->
                           let uu____15891 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15891)
                     in
                  let uu____15892 =
                    let uu____15905 = maybe_eta t1  in
                    let uu____15910 = maybe_eta t2  in
                    (uu____15905, uu____15910)  in
                  (match uu____15892 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___194_15934 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___194_15934.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___194_15934.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___194_15934.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___194_15934.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___194_15934.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___194_15934.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___194_15934.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___194_15934.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15945 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15945
                       then
                         let uu____15946 = destruct_flex_t not_abs wl  in
                         (match uu____15946 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_15961 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_15961.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_15961.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_15961.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_15961.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_15961.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_15961.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_15961.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_15961.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____15973 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15973
                       then
                         let uu____15974 = destruct_flex_t not_abs wl  in
                         (match uu____15974 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_15989 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_15989.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_15989.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_15989.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_15989.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_15989.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_15989.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_15989.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_15989.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____15991 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16004,FStar_Syntax_Syntax.Tm_abs uu____16005) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16032 -> true
                    | uu____16049 -> false  in
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
                      (let uu____16090 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___193_16098 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___193_16098.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___193_16098.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___193_16098.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___193_16098.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___193_16098.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___193_16098.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___193_16098.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___193_16098.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___193_16098.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___193_16098.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___193_16098.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___193_16098.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___193_16098.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___193_16098.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___193_16098.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___193_16098.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___193_16098.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___193_16098.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___193_16098.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___193_16098.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___193_16098.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___193_16098.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___193_16098.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___193_16098.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___193_16098.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___193_16098.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___193_16098.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___193_16098.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___193_16098.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___193_16098.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___193_16098.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___193_16098.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___193_16098.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___193_16098.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___193_16098.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16090 with
                       | (uu____16101,ty,uu____16103) ->
                           let uu____16104 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16104)
                     in
                  let uu____16105 =
                    let uu____16118 = maybe_eta t1  in
                    let uu____16123 = maybe_eta t2  in
                    (uu____16118, uu____16123)  in
                  (match uu____16105 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___194_16147 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___194_16147.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___194_16147.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___194_16147.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___194_16147.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___194_16147.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___194_16147.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___194_16147.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___194_16147.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16158 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16158
                       then
                         let uu____16159 = destruct_flex_t not_abs wl  in
                         (match uu____16159 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16174 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16174.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16174.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16174.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16174.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16174.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16174.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16174.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16174.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16186 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16186
                       then
                         let uu____16187 = destruct_flex_t not_abs wl  in
                         (match uu____16187 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16202 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16202.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16202.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16202.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16202.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16202.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16202.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16202.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16202.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16204 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16232 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16232) &&
                       (let uu____16236 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16236))
                      &&
                      (let uu____16243 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16243 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___148_16255 =
                             match uu___148_16255 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16256 -> true
                             | uu____16257 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16258 -> false)
                     in
                  let uu____16259 = as_refinement should_delta env wl t1  in
                  (match uu____16259 with
                   | (x11,phi1) ->
                       let uu____16266 = as_refinement should_delta env wl t2
                          in
                       (match uu____16266 with
                        | (x21,phi21) ->
                            let uu____16273 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16273 with
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
                                   let uu____16339 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16339
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16351 =
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
                                   let uu____16362 =
                                     let uu____16367 =
                                       let uu____16374 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16374]  in
                                     mk_t_problem wl1 uu____16367 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16362 with
                                    | (ref_prob,wl2) ->
                                        let uu____16389 =
                                          solve env1
                                            (let uu___196_16391 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___196_16391.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___196_16391.smt_ok);
                                               tcenv = (uu___196_16391.tcenv);
                                               wl_implicits =
                                                 (uu___196_16391.wl_implicits)
                                             })
                                           in
                                        (match uu____16389 with
                                         | Failed uu____16398 -> fallback ()
                                         | Success uu____16403 ->
                                             let guard =
                                               let uu____16411 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16411
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___197_16420 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___197_16420.attempting);
                                                 wl_deferred =
                                                   (uu___197_16420.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___197_16420.defer_ok);
                                                 smt_ok =
                                                   (uu___197_16420.smt_ok);
                                                 tcenv =
                                                   (uu___197_16420.tcenv);
                                                 wl_implicits =
                                                   (uu___197_16420.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16422,FStar_Syntax_Syntax.Tm_uvar uu____16423) ->
                  let uu____16452 = destruct_flex_t t1 wl  in
                  (match uu____16452 with
                   | (f1,wl1) ->
                       let uu____16459 = destruct_flex_t t2 wl1  in
                       (match uu____16459 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16466;
                    FStar_Syntax_Syntax.pos = uu____16467;
                    FStar_Syntax_Syntax.vars = uu____16468;_},uu____16469),FStar_Syntax_Syntax.Tm_uvar
                 uu____16470) ->
                  let uu____16519 = destruct_flex_t t1 wl  in
                  (match uu____16519 with
                   | (f1,wl1) ->
                       let uu____16526 = destruct_flex_t t2 wl1  in
                       (match uu____16526 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16533,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16534;
                    FStar_Syntax_Syntax.pos = uu____16535;
                    FStar_Syntax_Syntax.vars = uu____16536;_},uu____16537))
                  ->
                  let uu____16586 = destruct_flex_t t1 wl  in
                  (match uu____16586 with
                   | (f1,wl1) ->
                       let uu____16593 = destruct_flex_t t2 wl1  in
                       (match uu____16593 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16600;
                    FStar_Syntax_Syntax.pos = uu____16601;
                    FStar_Syntax_Syntax.vars = uu____16602;_},uu____16603),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16604;
                    FStar_Syntax_Syntax.pos = uu____16605;
                    FStar_Syntax_Syntax.vars = uu____16606;_},uu____16607))
                  ->
                  let uu____16676 = destruct_flex_t t1 wl  in
                  (match uu____16676 with
                   | (f1,wl1) ->
                       let uu____16683 = destruct_flex_t t2 wl1  in
                       (match uu____16683 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16690,uu____16691) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16706 = destruct_flex_t t1 wl  in
                  (match uu____16706 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16713;
                    FStar_Syntax_Syntax.pos = uu____16714;
                    FStar_Syntax_Syntax.vars = uu____16715;_},uu____16716),uu____16717)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16752 = destruct_flex_t t1 wl  in
                  (match uu____16752 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____16759,FStar_Syntax_Syntax.Tm_uvar uu____16760) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____16775,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16776;
                    FStar_Syntax_Syntax.pos = uu____16777;
                    FStar_Syntax_Syntax.vars = uu____16778;_},uu____16779))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16814,FStar_Syntax_Syntax.Tm_arrow uu____16815) ->
                  solve_t' env
                    (let uu___198_16843 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16843.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16843.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___198_16843.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___198_16843.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16843.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___198_16843.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16843.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16843.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16843.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16844;
                    FStar_Syntax_Syntax.pos = uu____16845;
                    FStar_Syntax_Syntax.vars = uu____16846;_},uu____16847),FStar_Syntax_Syntax.Tm_arrow
                 uu____16848) ->
                  solve_t' env
                    (let uu___198_16896 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16896.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16896.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___198_16896.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___198_16896.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16896.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___198_16896.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16896.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16896.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16896.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____16897,FStar_Syntax_Syntax.Tm_uvar uu____16898) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____16913,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16914;
                    FStar_Syntax_Syntax.pos = uu____16915;
                    FStar_Syntax_Syntax.vars = uu____16916;_},uu____16917))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____16952,uu____16953) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16968;
                    FStar_Syntax_Syntax.pos = uu____16969;
                    FStar_Syntax_Syntax.vars = uu____16970;_},uu____16971),uu____16972)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17007,uu____17008) ->
                  let t21 =
                    let uu____17016 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17016  in
                  solve_t env
                    (let uu___199_17042 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___199_17042.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___199_17042.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___199_17042.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___199_17042.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___199_17042.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___199_17042.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___199_17042.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___199_17042.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___199_17042.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17043,FStar_Syntax_Syntax.Tm_refine uu____17044) ->
                  let t11 =
                    let uu____17052 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17052  in
                  solve_t env
                    (let uu___200_17078 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___200_17078.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___200_17078.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___200_17078.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___200_17078.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___200_17078.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___200_17078.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___200_17078.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___200_17078.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___200_17078.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____17155 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____17155 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____17376 = br1  in
                             (match uu____17376 with
                              | (p1,w1,uu____17401) ->
                                  let uu____17418 = br2  in
                                  (match uu____17418 with
                                   | (p2,w2,uu____17437) ->
                                       let uu____17442 =
                                         let uu____17443 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____17443  in
                                       if uu____17442
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____17459 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____17459 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____17492 = br2  in
                                              (match uu____17492 with
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
                                                     let uu____17527 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____17527
                                                      in
                                                   let uu____17538 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____17561,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____17578) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____17621 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____17621
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____17538
                                                     (fun uu____17663  ->
                                                        match uu____17663
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____17684 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____17684
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____17699
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____17699
                                                                   (fun
                                                                    uu____17723
                                                                     ->
                                                                    match uu____17723
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
                         | uu____17808 -> FStar_Pervasives_Native.None  in
                       let uu____17845 = solve_branches wl1 brs1 brs2  in
                       (match uu____17845 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____17876,uu____17877) ->
                  let head1 =
                    let uu____17901 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17901
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17941 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17941
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17981 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____17981
                    then
                      let uu____17982 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17983 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17984 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17982 uu____17983 uu____17984
                    else ());
                   (let uu____17986 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17986
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17993 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17993
                       then
                         let uu____17994 =
                           let uu____18001 =
                             let uu____18002 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18002 = FStar_Syntax_Util.Equal  in
                           if uu____18001
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18012 = mk_eq2 wl orig t1 t2  in
                              match uu____18012 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17994 with
                         | (guard,wl1) ->
                             let uu____18033 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18033
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18036,uu____18037) ->
                  let head1 =
                    let uu____18045 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18045
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18085 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18085
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18125 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18125
                    then
                      let uu____18126 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18127 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18128 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18126 uu____18127 uu____18128
                    else ());
                   (let uu____18130 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18130
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18137 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18137
                       then
                         let uu____18138 =
                           let uu____18145 =
                             let uu____18146 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18146 = FStar_Syntax_Util.Equal  in
                           if uu____18145
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18156 = mk_eq2 wl orig t1 t2  in
                              match uu____18156 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18138 with
                         | (guard,wl1) ->
                             let uu____18177 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18177
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18180,uu____18181) ->
                  let head1 =
                    let uu____18183 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18183
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18223 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18223
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18263 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18263
                    then
                      let uu____18264 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18265 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18266 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18264 uu____18265 uu____18266
                    else ());
                   (let uu____18268 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18268
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18275 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18275
                       then
                         let uu____18276 =
                           let uu____18283 =
                             let uu____18284 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18284 = FStar_Syntax_Util.Equal  in
                           if uu____18283
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18294 = mk_eq2 wl orig t1 t2  in
                              match uu____18294 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18276 with
                         | (guard,wl1) ->
                             let uu____18315 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18315
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18318,uu____18319) ->
                  let head1 =
                    let uu____18321 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18321
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18361 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18361
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18401 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18401
                    then
                      let uu____18402 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18403 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18404 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18402 uu____18403 uu____18404
                    else ());
                   (let uu____18406 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18406
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18413 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18413
                       then
                         let uu____18414 =
                           let uu____18421 =
                             let uu____18422 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18422 = FStar_Syntax_Util.Equal  in
                           if uu____18421
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18432 = mk_eq2 wl orig t1 t2  in
                              match uu____18432 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18414 with
                         | (guard,wl1) ->
                             let uu____18453 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18453
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18456,uu____18457) ->
                  let head1 =
                    let uu____18459 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18459
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18499 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18499
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18539 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18539
                    then
                      let uu____18540 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18541 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18542 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18540 uu____18541 uu____18542
                    else ());
                   (let uu____18544 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18544
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18551 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18551
                       then
                         let uu____18552 =
                           let uu____18559 =
                             let uu____18560 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18560 = FStar_Syntax_Util.Equal  in
                           if uu____18559
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18570 = mk_eq2 wl orig t1 t2  in
                              match uu____18570 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18552 with
                         | (guard,wl1) ->
                             let uu____18591 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18591
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____18594,uu____18595) ->
                  let head1 =
                    let uu____18611 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18611
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18651 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18651
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18691 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18691
                    then
                      let uu____18692 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18693 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18694 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18692 uu____18693 uu____18694
                    else ());
                   (let uu____18696 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18696
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18703 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18703
                       then
                         let uu____18704 =
                           let uu____18711 =
                             let uu____18712 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18712 = FStar_Syntax_Util.Equal  in
                           if uu____18711
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18722 = mk_eq2 wl orig t1 t2  in
                              match uu____18722 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18704 with
                         | (guard,wl1) ->
                             let uu____18743 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18743
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18746,FStar_Syntax_Syntax.Tm_match uu____18747) ->
                  let head1 =
                    let uu____18771 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18771
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18811 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18811
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18851 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18851
                    then
                      let uu____18852 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18853 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18854 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18852 uu____18853 uu____18854
                    else ());
                   (let uu____18856 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18856
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18863 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18863
                       then
                         let uu____18864 =
                           let uu____18871 =
                             let uu____18872 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18872 = FStar_Syntax_Util.Equal  in
                           if uu____18871
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18882 = mk_eq2 wl orig t1 t2  in
                              match uu____18882 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18864 with
                         | (guard,wl1) ->
                             let uu____18903 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18903
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18906,FStar_Syntax_Syntax.Tm_uinst uu____18907) ->
                  let head1 =
                    let uu____18915 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18915
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18955 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18955
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18995 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18995
                    then
                      let uu____18996 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18997 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18998 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18996 uu____18997 uu____18998
                    else ());
                   (let uu____19000 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19000
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19007 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19007
                       then
                         let uu____19008 =
                           let uu____19015 =
                             let uu____19016 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19016 = FStar_Syntax_Util.Equal  in
                           if uu____19015
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19026 = mk_eq2 wl orig t1 t2  in
                              match uu____19026 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19008 with
                         | (guard,wl1) ->
                             let uu____19047 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19047
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19050,FStar_Syntax_Syntax.Tm_name uu____19051) ->
                  let head1 =
                    let uu____19053 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19053
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19093 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19093
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19133 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19133
                    then
                      let uu____19134 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19135 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19136 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19134 uu____19135 uu____19136
                    else ());
                   (let uu____19138 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19138
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19145 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19145
                       then
                         let uu____19146 =
                           let uu____19153 =
                             let uu____19154 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19154 = FStar_Syntax_Util.Equal  in
                           if uu____19153
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19164 = mk_eq2 wl orig t1 t2  in
                              match uu____19164 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19146 with
                         | (guard,wl1) ->
                             let uu____19185 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19185
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19188,FStar_Syntax_Syntax.Tm_constant uu____19189) ->
                  let head1 =
                    let uu____19191 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19191
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19231 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19231
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19271 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19271
                    then
                      let uu____19272 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19273 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19274 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19272 uu____19273 uu____19274
                    else ());
                   (let uu____19276 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19276
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19283 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19283
                       then
                         let uu____19284 =
                           let uu____19291 =
                             let uu____19292 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19292 = FStar_Syntax_Util.Equal  in
                           if uu____19291
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19302 = mk_eq2 wl orig t1 t2  in
                              match uu____19302 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19284 with
                         | (guard,wl1) ->
                             let uu____19323 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19323
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19326,FStar_Syntax_Syntax.Tm_fvar uu____19327) ->
                  let head1 =
                    let uu____19329 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19329
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19369 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19369
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19409 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19409
                    then
                      let uu____19410 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19411 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19412 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19410 uu____19411 uu____19412
                    else ());
                   (let uu____19414 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19414
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19421 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19421
                       then
                         let uu____19422 =
                           let uu____19429 =
                             let uu____19430 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19430 = FStar_Syntax_Util.Equal  in
                           if uu____19429
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19440 = mk_eq2 wl orig t1 t2  in
                              match uu____19440 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19422 with
                         | (guard,wl1) ->
                             let uu____19461 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19461
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19464,FStar_Syntax_Syntax.Tm_app uu____19465) ->
                  let head1 =
                    let uu____19481 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19481
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19521 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19521
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19561 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19561
                    then
                      let uu____19562 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19563 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19564 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19562 uu____19563 uu____19564
                    else ());
                   (let uu____19566 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19566
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19573 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19573
                       then
                         let uu____19574 =
                           let uu____19581 =
                             let uu____19582 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19582 = FStar_Syntax_Util.Equal  in
                           if uu____19581
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19592 = mk_eq2 wl orig t1 t2  in
                              match uu____19592 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19574 with
                         | (guard,wl1) ->
                             let uu____19613 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19613
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____19616,FStar_Syntax_Syntax.Tm_let uu____19617) ->
                  let uu____19642 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____19642
                  then
                    let uu____19643 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____19643
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____19645,uu____19646) ->
                  let uu____19659 =
                    let uu____19664 =
                      let uu____19665 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19666 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19667 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19668 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19665 uu____19666 uu____19667 uu____19668
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19664)
                     in
                  FStar_Errors.raise_error uu____19659
                    t1.FStar_Syntax_Syntax.pos
              | (uu____19669,FStar_Syntax_Syntax.Tm_let uu____19670) ->
                  let uu____19683 =
                    let uu____19688 =
                      let uu____19689 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19690 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19691 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19692 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19689 uu____19690 uu____19691 uu____19692
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19688)
                     in
                  FStar_Errors.raise_error uu____19683
                    t1.FStar_Syntax_Syntax.pos
              | uu____19693 -> giveup env "head tag mismatch" orig))))

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
          (let uu____19752 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____19752
           then
             let uu____19753 =
               let uu____19754 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____19754  in
             let uu____19755 =
               let uu____19756 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____19756  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____19753 uu____19755
           else ());
          (let uu____19758 =
             let uu____19759 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____19759  in
           if uu____19758
           then
             let uu____19760 =
               let uu____19761 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____19762 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____19761 uu____19762
                in
             giveup env uu____19760 orig
           else
             (let uu____19764 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____19764 with
              | (ret_sub_prob,wl1) ->
                  let uu____19771 =
                    FStar_List.fold_right2
                      (fun uu____19804  ->
                         fun uu____19805  ->
                           fun uu____19806  ->
                             match (uu____19804, uu____19805, uu____19806)
                             with
                             | ((a1,uu____19842),(a2,uu____19844),(arg_sub_probs,wl2))
                                 ->
                                 let uu____19865 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____19865 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____19771 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____19894 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____19894  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____19924 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____19927)::[] -> wp1
              | uu____19944 ->
                  let uu____19953 =
                    let uu____19954 =
                      let uu____19955 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____19955  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____19954
                     in
                  failwith uu____19953
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____19961 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____19961]
              | x -> x  in
            let uu____19963 =
              let uu____19972 =
                let uu____19979 =
                  let uu____19980 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____19980 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____19979  in
              [uu____19972]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____19963;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____19993 = lift_c1 ()  in solve_eq uu____19993 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___149_19999  ->
                       match uu___149_19999 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20000 -> false))
                in
             let uu____20001 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20027)::uu____20028,(wp2,uu____20030)::uu____20031)
                   -> (wp1, wp2)
               | uu____20084 ->
                   let uu____20105 =
                     let uu____20110 =
                       let uu____20111 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20112 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20111 uu____20112
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20110)
                      in
                   FStar_Errors.raise_error uu____20105
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20001 with
             | (wpc1,wpc2) ->
                 let uu____20119 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20119
                 then
                   let uu____20122 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20122 wl
                 else
                   (let uu____20124 =
                      let uu____20131 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20131  in
                    match uu____20124 with
                    | (c2_decl,qualifiers) ->
                        let uu____20152 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20152
                        then
                          let c1_repr =
                            let uu____20156 =
                              let uu____20157 =
                                let uu____20158 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20158  in
                              let uu____20159 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20157 uu____20159
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20156
                             in
                          let c2_repr =
                            let uu____20161 =
                              let uu____20162 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20163 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20162 uu____20163
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20161
                             in
                          let uu____20164 =
                            let uu____20169 =
                              let uu____20170 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20171 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20170 uu____20171
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20169
                             in
                          (match uu____20164 with
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
                                 ((let uu____20185 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20185
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20188 =
                                     let uu____20195 =
                                       let uu____20196 =
                                         let uu____20211 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20214 =
                                           let uu____20223 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20230 =
                                             let uu____20239 =
                                               let uu____20246 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20246
                                                in
                                             [uu____20239]  in
                                           uu____20223 :: uu____20230  in
                                         (uu____20211, uu____20214)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20196
                                        in
                                     FStar_Syntax_Syntax.mk uu____20195  in
                                   uu____20188 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20281 =
                                    let uu____20288 =
                                      let uu____20289 =
                                        let uu____20304 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20307 =
                                          let uu____20316 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20323 =
                                            let uu____20332 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20339 =
                                              let uu____20348 =
                                                let uu____20355 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20355
                                                 in
                                              [uu____20348]  in
                                            uu____20332 :: uu____20339  in
                                          uu____20316 :: uu____20323  in
                                        (uu____20304, uu____20307)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20289
                                       in
                                    FStar_Syntax_Syntax.mk uu____20288  in
                                  uu____20281 FStar_Pervasives_Native.None r)
                              in
                           let uu____20393 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20393 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20401 =
                                   let uu____20404 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____20404
                                    in
                                 solve_prob orig uu____20401 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____20411 = FStar_Util.physical_equality c1 c2  in
        if uu____20411
        then
          let uu____20412 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20412
        else
          ((let uu____20415 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20415
            then
              let uu____20416 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20417 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20416
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20417
            else ());
           (let uu____20419 =
              let uu____20428 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20431 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20428, uu____20431)  in
            match uu____20419 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20449),FStar_Syntax_Syntax.Total
                    (t2,uu____20451)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20468 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20468 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20469,FStar_Syntax_Syntax.Total uu____20470) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20488),FStar_Syntax_Syntax.Total
                    (t2,uu____20490)) ->
                     let uu____20507 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20507 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20509),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20511)) ->
                     let uu____20528 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20528 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20530),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20532)) ->
                     let uu____20549 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20549 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20550,FStar_Syntax_Syntax.Comp uu____20551) ->
                     let uu____20560 =
                       let uu___201_20563 = problem  in
                       let uu____20566 =
                         let uu____20567 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20567
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20563.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20566;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20563.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_20563.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_20563.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20563.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20563.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20563.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20563.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20563.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20560 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20568,FStar_Syntax_Syntax.Comp uu____20569) ->
                     let uu____20578 =
                       let uu___201_20581 = problem  in
                       let uu____20584 =
                         let uu____20585 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20585
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20581.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20584;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20581.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_20581.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_20581.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20581.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20581.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20581.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20581.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20581.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20578 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20586,FStar_Syntax_Syntax.GTotal uu____20587) ->
                     let uu____20596 =
                       let uu___202_20599 = problem  in
                       let uu____20602 =
                         let uu____20603 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20603
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20599.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_20599.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20599.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20602;
                         FStar_TypeChecker_Common.element =
                           (uu___202_20599.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20599.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20599.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20599.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20599.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20599.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20596 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20604,FStar_Syntax_Syntax.Total uu____20605) ->
                     let uu____20614 =
                       let uu___202_20617 = problem  in
                       let uu____20620 =
                         let uu____20621 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20621
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20617.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_20617.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20617.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20620;
                         FStar_TypeChecker_Common.element =
                           (uu___202_20617.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20617.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20617.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20617.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20617.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20617.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20614 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20622,FStar_Syntax_Syntax.Comp uu____20623) ->
                     let uu____20624 =
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
                     if uu____20624
                     then
                       let uu____20625 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____20625 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20629 =
                            let uu____20634 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____20634
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20640 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____20641 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____20640, uu____20641))
                             in
                          match uu____20629 with
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
                           (let uu____20648 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____20648
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20650 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____20650 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20653 =
                                  let uu____20654 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____20655 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____20654 uu____20655
                                   in
                                giveup env uu____20653 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____20662 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20695  ->
              match uu____20695 with
              | (uu____20706,tm,uu____20708,uu____20709,uu____20710) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____20662 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____20743 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____20743 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____20761 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____20789  ->
                match uu____20789 with
                | (u1,u2) ->
                    let uu____20796 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____20797 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____20796 uu____20797))
         in
      FStar_All.pipe_right uu____20761 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____20824,[])) -> "{}"
      | uu____20849 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____20872 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____20872
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____20875 =
              FStar_List.map
                (fun uu____20885  ->
                   match uu____20885 with
                   | (uu____20890,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____20875 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____20895 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____20895 imps
  
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
                  let uu____20948 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____20948
                  then
                    let uu____20949 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____20950 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____20949
                      (rel_to_string rel) uu____20950
                  else "TOP"  in
                let uu____20952 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____20952 with
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
              let uu____21009 =
                let uu____21012 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____21012
                 in
              FStar_Syntax_Syntax.new_bv uu____21009 t1  in
            let uu____21015 =
              let uu____21020 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21020
               in
            match uu____21015 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____21076 = FStar_Options.eager_inference ()  in
          if uu____21076
          then
            let uu___203_21077 = probs  in
            {
              attempting = (uu___203_21077.attempting);
              wl_deferred = (uu___203_21077.wl_deferred);
              ctr = (uu___203_21077.ctr);
              defer_ok = false;
              smt_ok = (uu___203_21077.smt_ok);
              tcenv = (uu___203_21077.tcenv);
              wl_implicits = (uu___203_21077.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21097 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21097
              then
                let uu____21098 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21098
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
          ((let uu____21120 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21120
            then
              let uu____21121 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21121
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21125 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21125
             then
               let uu____21126 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21126
             else ());
            (let f2 =
               let uu____21129 =
                 let uu____21130 = FStar_Syntax_Util.unmeta f1  in
                 uu____21130.FStar_Syntax_Syntax.n  in
               match uu____21129 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21134 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___204_21135 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___204_21135.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___204_21135.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___204_21135.FStar_TypeChecker_Env.implicits)
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
            let uu____21249 =
              let uu____21250 =
                let uu____21251 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21251;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21250  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____21249
  
let with_guard_no_simp :
  'Auu____21266 .
    'Auu____21266 ->
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
            let uu____21289 =
              let uu____21290 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21290;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21289
  
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
          (let uu____21330 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21330
           then
             let uu____21331 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21332 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21331
               uu____21332
           else ());
          (let uu____21334 =
             let uu____21339 = empty_worklist env  in
             let uu____21340 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____21339 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____21340
              in
           match uu____21334 with
           | (prob,wl) ->
               let g =
                 let uu____21348 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21368  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21348  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21412 = try_teq true env t1 t2  in
        match uu____21412 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21416 = FStar_TypeChecker_Env.get_range env  in
              let uu____21417 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21416 uu____21417);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21424 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21424
              then
                let uu____21425 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21426 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21427 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21425
                  uu____21426 uu____21427
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
          let uu____21449 = FStar_TypeChecker_Env.get_range env  in
          let uu____21450 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21449 uu____21450
  
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
        (let uu____21475 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21475
         then
           let uu____21476 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21477 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21476 uu____21477
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21480 =
           let uu____21487 = empty_worklist env  in
           let uu____21488 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____21487 env c1 rel c2 FStar_Pervasives_Native.None
             uu____21488 "sub_comp"
            in
         match uu____21480 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21498 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21518  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21498)
  
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
      fun uu____21573  ->
        match uu____21573 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21616 =
                 let uu____21621 =
                   let uu____21622 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21623 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21622 uu____21623
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21621)  in
               let uu____21624 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21616 uu____21624)
               in
            let equiv1 v1 v' =
              let uu____21636 =
                let uu____21641 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21642 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21641, uu____21642)  in
              match uu____21636 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21661 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21691 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____21691 with
                      | FStar_Syntax_Syntax.U_unif uu____21698 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21727  ->
                                    match uu____21727 with
                                    | (u,v') ->
                                        let uu____21736 = equiv1 v1 v'  in
                                        if uu____21736
                                        then
                                          let uu____21739 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____21739 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____21755 -> []))
               in
            let uu____21760 =
              let wl =
                let uu___205_21764 = empty_worklist env  in
                {
                  attempting = (uu___205_21764.attempting);
                  wl_deferred = (uu___205_21764.wl_deferred);
                  ctr = (uu___205_21764.ctr);
                  defer_ok = false;
                  smt_ok = (uu___205_21764.smt_ok);
                  tcenv = (uu___205_21764.tcenv);
                  wl_implicits = (uu___205_21764.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21782  ->
                      match uu____21782 with
                      | (lb,v1) ->
                          let uu____21789 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____21789 with
                           | USolved wl1 -> ()
                           | uu____21791 -> fail1 lb v1)))
               in
            let rec check_ineq uu____21801 =
              match uu____21801 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21810) -> true
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
                      uu____21833,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21835,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21846) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21853,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21861 -> false)
               in
            let uu____21866 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21881  ->
                      match uu____21881 with
                      | (u,v1) ->
                          let uu____21888 = check_ineq (u, v1)  in
                          if uu____21888
                          then true
                          else
                            ((let uu____21891 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____21891
                              then
                                let uu____21892 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____21893 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____21892
                                  uu____21893
                              else ());
                             false)))
               in
            if uu____21866
            then ()
            else
              ((let uu____21897 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____21897
                then
                  ((let uu____21899 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21899);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21909 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21909))
                else ());
               (let uu____21919 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____21919))
  
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
        let fail1 uu____21986 =
          match uu____21986 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___206_22007 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___206_22007.attempting);
            wl_deferred = (uu___206_22007.wl_deferred);
            ctr = (uu___206_22007.ctr);
            defer_ok;
            smt_ok = (uu___206_22007.smt_ok);
            tcenv = (uu___206_22007.tcenv);
            wl_implicits = (uu___206_22007.wl_implicits)
          }  in
        (let uu____22009 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22009
         then
           let uu____22010 = FStar_Util.string_of_bool defer_ok  in
           let uu____22011 = wl_to_string wl  in
           let uu____22012 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22010 uu____22011 uu____22012
         else ());
        (let g1 =
           let uu____22025 = solve_and_commit env wl fail1  in
           match uu____22025 with
           | FStar_Pervasives_Native.Some
               (uu____22032::uu____22033,uu____22034) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___207_22059 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___207_22059.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___207_22059.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22070 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___208_22078 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___208_22078.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___208_22078.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___208_22078.FStar_TypeChecker_Env.implicits)
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
    let uu____22126 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22126 with
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
            let uu___209_22249 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___209_22249.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___209_22249.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___209_22249.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22250 =
            let uu____22251 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22251  in
          if uu____22250
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22259 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22260 =
                       let uu____22261 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22261
                        in
                     FStar_Errors.diag uu____22259 uu____22260)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22265 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22266 =
                        let uu____22267 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22267
                         in
                      FStar_Errors.diag uu____22265 uu____22266)
                   else ();
                   (let uu____22270 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22270 "discharge_guard'"
                      env vc1);
                   (let uu____22271 = check_trivial vc1  in
                    match uu____22271 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22278 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22279 =
                                let uu____22280 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22280
                                 in
                              FStar_Errors.diag uu____22278 uu____22279)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22285 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22286 =
                                let uu____22287 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22287
                                 in
                              FStar_Errors.diag uu____22285 uu____22286)
                           else ();
                           (let vcs =
                              let uu____22300 = FStar_Options.use_tactics ()
                                 in
                              if uu____22300
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22322  ->
                                     (let uu____22324 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____22324);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22367  ->
                                              match uu____22367 with
                                              | (env1,goal,opts) ->
                                                  let uu____22383 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22383, opts)))))
                              else
                                (let uu____22385 =
                                   let uu____22392 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22392)  in
                                 [uu____22385])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22429  ->
                                    match uu____22429 with
                                    | (env1,goal,opts) ->
                                        let uu____22445 = check_trivial goal
                                           in
                                        (match uu____22445 with
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
                                                (let uu____22453 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22454 =
                                                   let uu____22455 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22456 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22455 uu____22456
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22453 uu____22454)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22459 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22460 =
                                                   let uu____22461 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22461
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22459 uu____22460)
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
      let uu____22475 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22475 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22482 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22482
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22493 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22493 with
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
            let uu____22526 = FStar_Syntax_Util.head_and_args u  in
            match uu____22526 with
            | (hd1,uu____22542) ->
                let uu____22563 =
                  let uu____22564 = FStar_Syntax_Subst.compress u  in
                  uu____22564.FStar_Syntax_Syntax.n  in
                (match uu____22563 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____22567 -> true
                 | uu____22582 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____22602 = acc  in
            match uu____22602 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22664 = hd1  in
                     (match uu____22664 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____22681 = unresolved tm  in
                             if uu____22681
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___210_22694 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___210_22694.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___210_22694.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___210_22694.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___210_22694.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___210_22694.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___210_22694.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___210_22694.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___210_22694.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___210_22694.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___210_22694.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___210_22694.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___210_22694.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___210_22694.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___210_22694.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___210_22694.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___210_22694.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___210_22694.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___210_22694.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___210_22694.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___210_22694.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___210_22694.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___210_22694.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___210_22694.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___210_22694.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___210_22694.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___210_22694.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___210_22694.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___210_22694.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___210_22694.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___210_22694.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___210_22694.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___210_22694.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___210_22694.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___210_22694.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___210_22694.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___210_22694.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___210_22694.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___211_22697 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___211_22697.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___211_22697.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___211_22697.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___211_22697.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___211_22697.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___211_22697.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___211_22697.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___211_22697.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___211_22697.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___211_22697.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___211_22697.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___211_22697.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___211_22697.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___211_22697.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___211_22697.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___211_22697.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___211_22697.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___211_22697.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___211_22697.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___211_22697.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___211_22697.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___211_22697.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___211_22697.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___211_22697.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___211_22697.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___211_22697.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___211_22697.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___211_22697.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___211_22697.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___211_22697.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___211_22697.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___211_22697.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___211_22697.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___211_22697.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___211_22697.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___211_22697.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___211_22697.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____22700 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____22700
                                 then
                                   let uu____22701 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____22702 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____22703 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____22704 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____22701 uu____22702 uu____22703
                                     reason uu____22704
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e when FStar_Errors.handleable e ->
                                       ((let uu____22715 =
                                           let uu____22724 =
                                             let uu____22731 =
                                               let uu____22732 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____22733 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____22732 uu____22733
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____22731, r)
                                              in
                                           [uu____22724]  in
                                         FStar_Errors.add_errors uu____22715);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___214_22747 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___214_22747.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___214_22747.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___214_22747.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____22750 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____22757  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____22750 with
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
          let uu___215_22769 = g  in
          let uu____22770 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___215_22769.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___215_22769.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___215_22769.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____22770
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
        let uu____22824 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____22824 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22835 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____22835
      | (reason,e,ctx_u,r,should_check)::uu____22841 ->
          let uu____22864 =
            let uu____22869 =
              let uu____22870 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____22871 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____22872 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____22870 uu____22871 reason uu____22872
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____22869)
             in
          FStar_Errors.raise_error uu____22864 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___216_22883 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___216_22883.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___216_22883.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___216_22883.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____22898 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22898 with
      | FStar_Pervasives_Native.Some uu____22904 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22920 = try_teq false env t1 t2  in
        match uu____22920 with
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
        (let uu____22954 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22954
         then
           let uu____22955 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____22956 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22955
             uu____22956
         else ());
        (let uu____22958 =
           let uu____22965 = empty_worklist env  in
           new_t_prob uu____22965 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____22958 with
         | (prob,x,wl) ->
             let g =
               let uu____22978 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____22998  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____22978  in
             ((let uu____23028 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23028
               then
                 let uu____23029 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23030 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23031 =
                   let uu____23032 = FStar_Util.must g  in
                   guard_to_string env uu____23032  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23029 uu____23030 uu____23031
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
        let uu____23066 = check_subtyping env t1 t2  in
        match uu____23066 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23085 =
              let uu____23086 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23086 g  in
            FStar_Pervasives_Native.Some uu____23085
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23104 = check_subtyping env t1 t2  in
        match uu____23104 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23123 =
              let uu____23124 =
                let uu____23125 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23125]  in
              close_guard env uu____23124 g  in
            FStar_Pervasives_Native.Some uu____23123
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23154 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23154
         then
           let uu____23155 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23156 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23155
             uu____23156
         else ());
        (let uu____23158 =
           let uu____23165 = empty_worklist env  in
           new_t_prob uu____23165 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23158 with
         | (prob,x,wl) ->
             let g =
               let uu____23172 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23192  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23172  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23223 =
                      let uu____23224 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23224]  in
                    close_guard env uu____23223 g1  in
                  discharge_guard_nosmt env g2))
  