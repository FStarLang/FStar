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
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7717,FStar_Syntax_Syntax.Tm_uvar uu____7718)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7735,FStar_Syntax_Syntax.Tm_arrow uu____7736)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7766 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7766.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7766.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7766.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7766.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7766.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7766.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7766.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7766.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7766.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7769,FStar_Syntax_Syntax.Tm_type uu____7770)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7788 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7788.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7788.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7788.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7788.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7788.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7788.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7788.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7788.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7788.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7791,FStar_Syntax_Syntax.Tm_uvar uu____7792)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7810 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7810.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7810.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7810.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7810.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7810.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7810.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7810.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7810.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7810.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7813,FStar_Syntax_Syntax.Tm_uvar uu____7814)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7831,uu____7832)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7849,FStar_Syntax_Syntax.Tm_uvar uu____7850)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7867,uu____7868) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7581 with
                     | (rank,tp1) ->
                         let uu____7881 =
                           FStar_All.pipe_right
                             (let uu___169_7885 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___169_7885.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___169_7885.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___169_7885.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___169_7885.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___169_7885.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___169_7885.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___169_7885.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___169_7885.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___169_7885.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7881))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7891 =
            FStar_All.pipe_right
              (let uu___170_7895 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___170_7895.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___170_7895.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___170_7895.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___170_7895.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___170_7895.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___170_7895.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___170_7895.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___170_7895.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___170_7895.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7891)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____7956 probs =
      match uu____7956 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8037 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8058 = rank wl.tcenv hd1  in
               (match uu____8058 with
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
                      (let uu____8117 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8121 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8121)
                          in
                       if uu____8117
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
          let uu____8189 = FStar_Syntax_Util.head_and_args t  in
          match uu____8189 with
          | (hd1,uu____8205) ->
              let uu____8226 =
                let uu____8227 = FStar_Syntax_Subst.compress hd1  in
                uu____8227.FStar_Syntax_Syntax.n  in
              (match uu____8226 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8231) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8265  ->
                           match uu____8265 with
                           | (y,uu____8271) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8285  ->
                                       match uu____8285 with
                                       | (x,uu____8291) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8292 -> false)
           in
        let uu____8293 = rank tcenv p  in
        match uu____8293 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8300 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8327 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8341 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8355 -> false
  
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
                        let uu____8407 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8407 with
                        | (k,uu____8413) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8423 -> false)))
            | uu____8424 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8476 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8482 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8482 = (Prims.parse_int "0")))
                           in
                        if uu____8476 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8498 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8504 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8504 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8498)
               in
            let uu____8505 = filter1 u12  in
            let uu____8508 = filter1 u22  in (uu____8505, uu____8508)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8537 = filter_out_common_univs us1 us2  in
                (match uu____8537 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8596 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8596 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8599 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8609 =
                          let uu____8610 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8611 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8610
                            uu____8611
                           in
                        UFailed uu____8609))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8635 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8635 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8661 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8661 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8664 ->
                let uu____8669 =
                  let uu____8670 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8671 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8670
                    uu____8671 msg
                   in
                UFailed uu____8669
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8672,uu____8673) ->
              let uu____8674 =
                let uu____8675 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8676 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8675 uu____8676
                 in
              failwith uu____8674
          | (FStar_Syntax_Syntax.U_unknown ,uu____8677) ->
              let uu____8678 =
                let uu____8679 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8680 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8679 uu____8680
                 in
              failwith uu____8678
          | (uu____8681,FStar_Syntax_Syntax.U_bvar uu____8682) ->
              let uu____8683 =
                let uu____8684 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8685 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8684 uu____8685
                 in
              failwith uu____8683
          | (uu____8686,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8687 =
                let uu____8688 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8689 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8688 uu____8689
                 in
              failwith uu____8687
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8713 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8713
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8727 = occurs_univ v1 u3  in
              if uu____8727
              then
                let uu____8728 =
                  let uu____8729 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8730 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8729 uu____8730
                   in
                try_umax_components u11 u21 uu____8728
              else
                (let uu____8732 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8732)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8744 = occurs_univ v1 u3  in
              if uu____8744
              then
                let uu____8745 =
                  let uu____8746 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8747 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8746 uu____8747
                   in
                try_umax_components u11 u21 uu____8745
              else
                (let uu____8749 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8749)
          | (FStar_Syntax_Syntax.U_max uu____8750,uu____8751) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8757 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8757
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8759,FStar_Syntax_Syntax.U_max uu____8760) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8766 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8766
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8768,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8769,FStar_Syntax_Syntax.U_name
             uu____8770) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8771) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8772) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8773,FStar_Syntax_Syntax.U_succ
             uu____8774) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8775,FStar_Syntax_Syntax.U_zero
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
      let uu____8875 = bc1  in
      match uu____8875 with
      | (bs1,mk_cod1) ->
          let uu____8919 = bc2  in
          (match uu____8919 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9030 = aux xs ys  in
                     (match uu____9030 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9113 =
                       let uu____9120 = mk_cod1 xs  in ([], uu____9120)  in
                     let uu____9123 =
                       let uu____9130 = mk_cod2 ys  in ([], uu____9130)  in
                     (uu____9113, uu____9123)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____9153 'Auu____9154 'Auu____9155 .
    ('Auu____9153,'Auu____9154,'Auu____9155 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___143_9168  ->
    match uu___143_9168 with
    | (uu____9177,uu____9178,[]) -> true
    | uu____9181 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9212 = f  in
      match uu____9212 with
      | (uu____9219,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9220;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9221;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9224;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9225;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9226;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9278  ->
                 match uu____9278 with
                 | (y,uu____9284) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9406 =
                  let uu____9419 =
                    let uu____9422 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9422  in
                  ((FStar_List.rev pat_binders), uu____9419)  in
                FStar_Pervasives_Native.Some uu____9406
            | (uu____9449,[]) ->
                let uu____9472 =
                  let uu____9485 =
                    let uu____9488 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9488  in
                  ((FStar_List.rev pat_binders), uu____9485)  in
                FStar_Pervasives_Native.Some uu____9472
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9553 =
                  let uu____9554 = FStar_Syntax_Subst.compress a  in
                  uu____9554.FStar_Syntax_Syntax.n  in
                (match uu____9553 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9572 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9572
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___171_9593 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___171_9593.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___171_9593.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9597 =
                            let uu____9598 =
                              let uu____9605 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9605)  in
                            FStar_Syntax_Syntax.NT uu____9598  in
                          [uu____9597]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___172_9617 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___172_9617.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___172_9617.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9618 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9646 =
                  let uu____9659 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9659  in
                (match uu____9646 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9722 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9749 ->
               let uu____9750 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9750 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10026 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10026
       then
         let uu____10027 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10027
       else ());
      (let uu____10029 = next_prob probs  in
       match uu____10029 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___173_10056 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___173_10056.wl_deferred);
               ctr = (uu___173_10056.ctr);
               defer_ok = (uu___173_10056.defer_ok);
               smt_ok = (uu___173_10056.smt_ok);
               tcenv = (uu___173_10056.tcenv);
               wl_implicits = (uu___173_10056.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10063 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10063
                then
                  let uu____10064 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10064
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
                          (let uu___174_10069 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___174_10069.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___174_10069.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___174_10069.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___174_10069.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___174_10069.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___174_10069.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___174_10069.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___174_10069.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___174_10069.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10091 ->
                let uu____10100 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10159  ->
                          match uu____10159 with
                          | (c,uu____10167,uu____10168) -> c < probs.ctr))
                   in
                (match uu____10100 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10209 =
                            let uu____10214 =
                              FStar_List.map
                                (fun uu____10229  ->
                                   match uu____10229 with
                                   | (uu____10240,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10214, (probs.wl_implicits))  in
                          Success uu____10209
                      | uu____10243 ->
                          let uu____10252 =
                            let uu___175_10253 = probs  in
                            let uu____10254 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10273  ->
                                      match uu____10273 with
                                      | (uu____10280,uu____10281,y) -> y))
                               in
                            {
                              attempting = uu____10254;
                              wl_deferred = rest;
                              ctr = (uu___175_10253.ctr);
                              defer_ok = (uu___175_10253.defer_ok);
                              smt_ok = (uu___175_10253.smt_ok);
                              tcenv = (uu___175_10253.tcenv);
                              wl_implicits = (uu___175_10253.wl_implicits)
                            }  in
                          solve env uu____10252))))

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
            let uu____10288 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10288 with
            | USolved wl1 ->
                let uu____10290 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10290
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
                  let uu____10342 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10342 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10345 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10357;
                  FStar_Syntax_Syntax.vars = uu____10358;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10361;
                  FStar_Syntax_Syntax.vars = uu____10362;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10374,uu____10375) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10382,FStar_Syntax_Syntax.Tm_uinst uu____10383) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10390 -> USolved wl

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
            ((let uu____10400 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10400
              then
                let uu____10401 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10401 msg
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
              let uu____10486 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10486 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10538 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10538
               then
                 let uu____10539 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10540 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10539
                   uu____10540
               else ());
              (let uu____10542 = head_matches_delta env1 () t1 t2  in
               match uu____10542 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____10587 ->
                        let uu____10596 = eq_prob t1 t2 wl2  in
                        (match uu____10596 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____10643 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10658 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10659 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10658, uu____10659)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10664 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10665 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10664, uu____10665)
                           in
                        (match uu____10643 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10696 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10696 with
                               | (t1_hd,t1_args) ->
                                   let uu____10735 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10735 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____10789 =
                                             let uu____10796 =
                                               let uu____10805 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____10805 :: t1_args  in
                                             let uu____10818 =
                                               let uu____10825 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____10825 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____10866  ->
                                                  fun uu____10867  ->
                                                    fun uu____10868  ->
                                                      match (uu____10866,
                                                              uu____10867,
                                                              uu____10868)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____10910),
                                                         (a2,uu____10912)) ->
                                                          let uu____10937 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____10937
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____10796
                                               uu____10818
                                              in
                                           match uu____10789 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___176_10963 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___176_10963.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___176_10963.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10981 =
                                                 solve env1 wl'  in
                                               (match uu____10981 with
                                                | Success (uu____10984,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___177_10988 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___177_10988.attempting);
                                                           wl_deferred =
                                                             (uu___177_10988.wl_deferred);
                                                           ctr =
                                                             (uu___177_10988.ctr);
                                                           defer_ok =
                                                             (uu___177_10988.defer_ok);
                                                           smt_ok =
                                                             (uu___177_10988.smt_ok);
                                                           tcenv =
                                                             (uu___177_10988.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____10999 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11031 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11031 with
                               | (t1_base,p1_opt) ->
                                   let uu____11072 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11072 with
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
                                              let uu____11203 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____11203
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
                                              let uu____11233 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11233
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
                                              let uu____11263 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11263
                                          | uu____11266 -> t_base  in
                                        let uu____11283 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11283 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11297 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11297, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11304 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11304 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11345 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11345 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11386 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11386
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
                             let uu____11410 = combine t11 t21 wl2  in
                             (match uu____11410 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11443 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11443
                                    then
                                      let uu____11444 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11444
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11483 ts1 =
              match uu____11483 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11546 = pairwise out t wl2  in
                       (match uu____11546 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11582 =
              let uu____11593 = FStar_List.hd ts  in (uu____11593, [], wl1)
               in
            let uu____11602 = FStar_List.tl ts  in
            aux uu____11582 uu____11602  in
          let uu____11609 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11609 with
          | (this_flex,this_rigid) ->
              let uu____11621 =
                let uu____11622 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11622.FStar_Syntax_Syntax.n  in
              (match uu____11621 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11643 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11643
                   then
                     let uu____11644 = destruct_flex_t this_flex wl  in
                     (match uu____11644 with
                      | (flex,wl1) ->
                          let uu____11651 = quasi_pattern env flex  in
                          (match uu____11651 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11669 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11669
                                 then
                                   let uu____11670 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11670
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
                             ((let uu___178_11675 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___178_11675.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___178_11675.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___178_11675.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___178_11675.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___178_11675.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___178_11675.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___178_11675.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___178_11675.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___178_11675.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11676 ->
                   ((let uu____11678 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11678
                     then
                       let uu____11679 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11679
                     else ());
                    (let uu____11681 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11681 with
                     | (u,_args) ->
                         let uu____11718 =
                           let uu____11719 = FStar_Syntax_Subst.compress u
                              in
                           uu____11719.FStar_Syntax_Syntax.n  in
                         (match uu____11718 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____11750 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____11750 with
                                | (u',uu____11766) ->
                                    let uu____11787 =
                                      let uu____11788 = whnf env u'  in
                                      uu____11788.FStar_Syntax_Syntax.n  in
                                    (match uu____11787 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____11813 -> false)
                                 in
                              let uu____11814 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___144_11837  ->
                                        match uu___144_11837 with
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
                                             | uu____11846 -> false)
                                        | uu____11849 -> false))
                                 in
                              (match uu____11814 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____11863 = whnf env this_rigid
                                        in
                                     let uu____11864 =
                                       FStar_List.collect
                                         (fun uu___145_11870  ->
                                            match uu___145_11870 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____11876 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____11876]
                                            | uu____11878 -> []) bounds_probs
                                        in
                                     uu____11863 :: uu____11864  in
                                   let uu____11879 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____11879 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____11910 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____11925 =
                                              let uu____11926 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____11926.FStar_Syntax_Syntax.n
                                               in
                                            match uu____11925 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____11938 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____11938)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____11947 -> bound  in
                                          let uu____11948 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____11948)  in
                                        (match uu____11910 with
                                         | (bound_typ,(eq_prob,wl2)) ->
                                             ((let uu____11976 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____11976
                                               then
                                                 let wl' =
                                                   let uu___179_11978 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___179_11978.wl_deferred);
                                                     ctr =
                                                       (uu___179_11978.ctr);
                                                     defer_ok =
                                                       (uu___179_11978.defer_ok);
                                                     smt_ok =
                                                       (uu___179_11978.smt_ok);
                                                     tcenv =
                                                       (uu___179_11978.tcenv);
                                                     wl_implicits =
                                                       (uu___179_11978.wl_implicits)
                                                   }  in
                                                 let uu____11979 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____11979
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11982 =
                                                 solve_t env eq_prob
                                                   (let uu___180_11984 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___180_11984.wl_deferred);
                                                      ctr =
                                                        (uu___180_11984.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___180_11984.smt_ok);
                                                      tcenv =
                                                        (uu___180_11984.tcenv);
                                                      wl_implicits =
                                                        (uu___180_11984.wl_implicits)
                                                    })
                                                  in
                                               match uu____11982 with
                                               | Success uu____11985 ->
                                                   let wl3 =
                                                     let uu___181_11991 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___181_11991.wl_deferred);
                                                       ctr =
                                                         (uu___181_11991.ctr);
                                                       defer_ok =
                                                         (uu___181_11991.defer_ok);
                                                       smt_ok =
                                                         (uu___181_11991.smt_ok);
                                                       tcenv =
                                                         (uu___181_11991.tcenv);
                                                       wl_implicits =
                                                         (uu___181_11991.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____11995 =
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
                                                    (let uu____12007 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12007
                                                     then
                                                       let uu____12008 =
                                                         let uu____12009 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12009
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12008
                                                     else ());
                                                    (let uu____12015 =
                                                       let uu____12030 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12030)
                                                        in
                                                     match uu____12015 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12052))
                                                         ->
                                                         let uu____12077 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12077
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
                                                         let uu____12116 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12116
                                                          with
                                                          | (eq_prob1,wl3) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl3 tp x
                                                                  phi
                                                                 in
                                                              let wl4 =
                                                                let uu____12133
                                                                  =
                                                                  let uu____12138
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12138
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12133
                                                                  [] wl3
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl4))
                                                     | uu____12143 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12158 when flip ->
                              let uu____12159 =
                                let uu____12160 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a flex-rigid: %s"
                                  uu____12160
                                 in
                              failwith uu____12159
                          | uu____12161 ->
                              let uu____12162 =
                                let uu____12163 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a rigid-flex: %s"
                                  uu____12163
                                 in
                              failwith uu____12162))))

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
                      (fun uu____12191  ->
                         match uu____12191 with
                         | (x,i) ->
                             let uu____12202 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12202, i)) bs_lhs
                     in
                  let uu____12203 = lhs  in
                  match uu____12203 with
                  | (uu____12204,u_lhs,uu____12206) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12319 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12329 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12329, univ)
                             in
                          match uu____12319 with
                          | (k,univ) ->
                              let uu____12342 =
                                let uu____12349 =
                                  let uu____12352 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12352
                                   in
                                copy_uvar u_lhs uu____12349 wl2  in
                              (match uu____12342 with
                               | (uu____12365,u,wl3) ->
                                   let uu____12368 =
                                     let uu____12371 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12371
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12368, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12407 =
                              let uu____12420 =
                                let uu____12429 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12429 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12475  ->
                                   fun uu____12476  ->
                                     match (uu____12475, uu____12476) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12567 =
                                           let uu____12574 =
                                             let uu____12577 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12577
                                              in
                                           copy_uvar u_lhs uu____12574 wl2
                                            in
                                         (match uu____12567 with
                                          | (uu____12600,t_a,wl3) ->
                                              let uu____12603 =
                                                let uu____12610 =
                                                  let uu____12613 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12613
                                                   in
                                                copy_uvar u_lhs uu____12610
                                                  wl3
                                                 in
                                              (match uu____12603 with
                                               | (uu____12628,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12420
                                ([], wl1)
                               in
                            (match uu____12407 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___182_12689 = ct  in
                                   let uu____12690 =
                                     let uu____12693 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12693
                                      in
                                   let uu____12708 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___182_12689.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___182_12689.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12690;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12708;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___182_12689.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___183_12726 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___183_12726.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___183_12726.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12729 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12729 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12783 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12783 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12800 =
                                          let uu____12805 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12805)  in
                                        TERM uu____12800  in
                                      let uu____12806 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12806 with
                                       | (sub_prob,wl3) ->
                                           let uu____12817 =
                                             let uu____12818 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12818
                                              in
                                           solve env uu____12817))
                             | (x,imp)::formals2 ->
                                 let uu____12832 =
                                   let uu____12839 =
                                     let uu____12842 =
                                       let uu____12845 =
                                         let uu____12846 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____12846
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____12845
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____12842
                                      in
                                   copy_uvar u_lhs uu____12839 wl1  in
                                 (match uu____12832 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____12870 =
                                          let uu____12873 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12873
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12870 t_y
                                         in
                                      let uu____12874 =
                                        let uu____12877 =
                                          let uu____12880 =
                                            let uu____12881 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12881, imp)  in
                                          [uu____12880]  in
                                        FStar_List.append bs_terms
                                          uu____12877
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12874 formals2 wl2)
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
              (let uu____12923 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12923
               then
                 let uu____12924 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12925 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12924 (rel_to_string (p_rel orig)) uu____12925
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13030 = rhs wl1 scope env1 subst1  in
                     (match uu____13030 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13050 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13050
                            then
                              let uu____13051 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13051
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___184_13105 = hd1  in
                       let uu____13106 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___184_13105.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___184_13105.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13106
                       }  in
                     let hd21 =
                       let uu___185_13110 = hd2  in
                       let uu____13111 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___185_13110.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___185_13110.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13111
                       }  in
                     let uu____13114 =
                       let uu____13119 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13119
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13114 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13138 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13138
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13142 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13142 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13197 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13197
                                  in
                               ((let uu____13209 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13209
                                 then
                                   let uu____13210 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13211 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13210
                                     uu____13211
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13238 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13267 = aux wl [] env [] bs1 bs2  in
               match uu____13267 with
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
        (let uu____13318 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13318 wl)

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
              let uu____13332 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13332 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13362 = lhs1  in
              match uu____13362 with
              | (uu____13365,ctx_u,uu____13367) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13373 ->
                        let uu____13374 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13374 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13421 = quasi_pattern env1 lhs1  in
              match uu____13421 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13451) ->
                  let uu____13456 = lhs1  in
                  (match uu____13456 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13470 = occurs_check ctx_u rhs1  in
                       (match uu____13470 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13512 =
                                let uu____13519 =
                                  let uu____13520 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13520
                                   in
                                FStar_Util.Inl uu____13519  in
                              (uu____13512, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13540 =
                                 let uu____13541 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13541  in
                               if uu____13540
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13561 =
                                    let uu____13568 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13568  in
                                  let uu____13573 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13561, uu____13573)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13635  ->
                     match uu____13635 with
                     | (x,i) ->
                         let uu____13646 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13646, i)) bs_lhs
                 in
              let uu____13647 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13647 with
              | (rhs_hd,args) ->
                  let uu____13684 = FStar_Util.prefix args  in
                  (match uu____13684 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13742 = lhs1  in
                       (match uu____13742 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13746 =
                              let uu____13757 =
                                let uu____13764 =
                                  let uu____13767 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13767
                                   in
                                copy_uvar u_lhs uu____13764 wl1  in
                              match uu____13757 with
                              | (uu____13788,t_last_arg,wl2) ->
                                  let uu____13791 =
                                    let uu____13798 =
                                      let uu____13801 =
                                        let uu____13808 =
                                          let uu____13815 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____13815]  in
                                        FStar_List.append bs_lhs uu____13808
                                         in
                                      let uu____13832 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____13801
                                        uu____13832
                                       in
                                    copy_uvar u_lhs uu____13798 wl2  in
                                  (match uu____13791 with
                                   | (uu____13845,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13851 =
                                         let uu____13858 =
                                           let uu____13861 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____13861
                                            in
                                         copy_uvar u_lhs uu____13858 wl3  in
                                       (match uu____13851 with
                                        | (uu____13874,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13746 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13898 =
                                     let uu____13899 =
                                       let uu____13904 =
                                         let uu____13905 =
                                           let uu____13908 =
                                             let uu____13913 =
                                               let uu____13914 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13914]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13913
                                              in
                                           uu____13908
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13905
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13904)  in
                                     TERM uu____13899  in
                                   [uu____13898]  in
                                 let uu____13935 =
                                   let uu____13942 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____13942 with
                                   | (p1,wl3) ->
                                       let uu____13959 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____13959 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13935 with
                                  | (sub_probs,wl3) ->
                                      let uu____13986 =
                                        let uu____13987 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____13987  in
                                      solve env1 uu____13986))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14020 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14020 with
                | (uu____14035,args) ->
                    (match args with | [] -> false | uu____14063 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14078 =
                  let uu____14079 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14079.FStar_Syntax_Syntax.n  in
                match uu____14078 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14082 -> true
                | uu____14095 -> false  in
              let uu____14096 = quasi_pattern env1 lhs1  in
              match uu____14096 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14107 =
                    let uu____14108 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14108
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14107
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14115 = is_app rhs1  in
                  if uu____14115
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14117 = is_arrow rhs1  in
                     if uu____14117
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14119 =
                          let uu____14120 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14120
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14119))
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
                let uu____14123 = lhs  in
                (match uu____14123 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14127 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14127 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14142 =
                              let uu____14145 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14145
                               in
                            FStar_All.pipe_right uu____14142
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14160 = occurs_check ctx_uv rhs1  in
                          (match uu____14160 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14182 =
                                   let uu____14183 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14183
                                    in
                                 giveup_or_defer env orig wl uu____14182
                               else
                                 (let uu____14185 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14185
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14190 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14190
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14192 =
                                         let uu____14193 =
                                           names_to_string1 fvs2  in
                                         let uu____14194 =
                                           names_to_string1 fvs1  in
                                         let uu____14195 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14193 uu____14194
                                           uu____14195
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14192)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14201 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14205 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14205 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14228 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14228
                             | (FStar_Util.Inl msg,uu____14230) ->
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
                  (let uu____14259 =
                     let uu____14276 = quasi_pattern env lhs  in
                     let uu____14283 = quasi_pattern env rhs  in
                     (uu____14276, uu____14283)  in
                   match uu____14259 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14326 = lhs  in
                       (match uu____14326 with
                        | ({ FStar_Syntax_Syntax.n = uu____14327;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14329;_},u_lhs,uu____14331)
                            ->
                            let uu____14334 = rhs  in
                            (match uu____14334 with
                             | (uu____14335,u_rhs,uu____14337) ->
                                 let uu____14338 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14338
                                 then
                                   let uu____14339 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14339
                                 else
                                   (let uu____14341 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14341 with
                                    | (sub_prob,wl1) ->
                                        let uu____14352 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14352 with
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
                                             let uu____14380 =
                                               let uu____14387 =
                                                 let uu____14390 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14390
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
                                                 uu____14387
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____14380 with
                                              | (uu____14393,w,wl2) ->
                                                  let w_app =
                                                    let uu____14399 =
                                                      let uu____14404 =
                                                        FStar_List.map
                                                          (fun uu____14413 
                                                             ->
                                                             match uu____14413
                                                             with
                                                             | (z,uu____14419)
                                                                 ->
                                                                 let uu____14420
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14420)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14404
                                                       in
                                                    uu____14399
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14424 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14424
                                                    then
                                                      let uu____14425 =
                                                        let uu____14428 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14429 =
                                                          let uu____14432 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14433 =
                                                            let uu____14436 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14437 =
                                                              let uu____14440
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14445
                                                                =
                                                                let uu____14448
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14453
                                                                  =
                                                                  let uu____14456
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14456]
                                                                   in
                                                                uu____14448
                                                                  ::
                                                                  uu____14453
                                                                 in
                                                              uu____14440 ::
                                                                uu____14445
                                                               in
                                                            uu____14436 ::
                                                              uu____14437
                                                             in
                                                          uu____14432 ::
                                                            uu____14433
                                                           in
                                                        uu____14428 ::
                                                          uu____14429
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14425
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14462 =
                                                          let uu____14467 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14467)
                                                           in
                                                        TERM uu____14462  in
                                                      let uu____14468 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14468
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14473 =
                                                             let uu____14478
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
                                                               uu____14478)
                                                              in
                                                           TERM uu____14473
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14479 =
                                                      let uu____14480 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14480
                                                       in
                                                    solve env uu____14479)))))))
                   | uu____14481 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____14549 = head_matches_delta env1 wl1 t1 t2  in
           match uu____14549 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____14580,uu____14581) ->
                    let rec may_relate head3 =
                      let uu____14608 =
                        let uu____14609 = FStar_Syntax_Subst.compress head3
                           in
                        uu____14609.FStar_Syntax_Syntax.n  in
                      match uu____14608 with
                      | FStar_Syntax_Syntax.Tm_name uu____14612 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____14613 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14636;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____14637;
                            FStar_Syntax_Syntax.fv_qual = uu____14638;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14641;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____14642;
                            FStar_Syntax_Syntax.fv_qual = uu____14643;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____14647,uu____14648) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____14690) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____14696) ->
                          may_relate t
                      | uu____14701 -> false  in
                    let uu____14702 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____14702
                    then
                      let uu____14703 =
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
                                 let uu____14735 =
                                   let uu____14736 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____14736 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____14735
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____14741 = has_type_guard t1 t2  in
                             (uu____14741, wl1)
                           else
                             (let uu____14747 = has_type_guard t2 t1  in
                              (uu____14747, wl1)))
                         in
                      (match uu____14703 with
                       | (guard,wl2) ->
                           let uu____14754 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____14754)
                    else
                      (let uu____14756 =
                         let uu____14757 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14758 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____14757 uu____14758
                          in
                       giveup env1 uu____14756 orig)
                | (uu____14759,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___186_14773 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___186_14773.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___186_14773.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___186_14773.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___186_14773.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___186_14773.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___186_14773.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___186_14773.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___186_14773.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____14774,FStar_Pervasives_Native.None ) ->
                    ((let uu____14786 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14786
                      then
                        let uu____14787 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____14788 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____14789 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____14790 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____14787 uu____14788 uu____14789 uu____14790
                      else ());
                     (let uu____14792 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____14792 with
                      | (head11,args1) ->
                          let uu____14829 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____14829 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____14883 =
                                   let uu____14884 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____14885 = args_to_string args1  in
                                   let uu____14886 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____14887 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____14884 uu____14885 uu____14886
                                     uu____14887
                                    in
                                 giveup env1 uu____14883 orig
                               else
                                 (let uu____14889 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____14896 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____14896 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____14889
                                  then
                                    let uu____14897 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____14897 with
                                    | USolved wl2 ->
                                        let uu____14899 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____14899
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____14903 =
                                       base_and_refinement env1 t1  in
                                     match uu____14903 with
                                     | (base1,refinement1) ->
                                         let uu____14928 =
                                           base_and_refinement env1 t2  in
                                         (match uu____14928 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____14985 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____14985 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____14989 =
                                                          FStar_List.fold_right2
                                                            (fun uu____15022 
                                                               ->
                                                               fun
                                                                 uu____15023 
                                                                 ->
                                                                 fun
                                                                   uu____15024
                                                                    ->
                                                                   match 
                                                                    (uu____15022,
                                                                    uu____15023,
                                                                    uu____15024)
                                                                   with
                                                                   | 
                                                                   ((a,uu____15060),
                                                                    (a',uu____15062),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____15083
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____15083
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
                                                        (match uu____14989
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____15111
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____15111
                                                               then
                                                                 let uu____15112
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____15112
                                                               else ());
                                                              (let formula =
                                                                 let uu____15117
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____15117
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
                                               | uu____15125 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___187_15165 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___187_15165.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15168 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15168
          then
            let uu____15169 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15169
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15174 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15174
              then
                let uu____15175 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15176 =
                  let uu____15177 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15178 =
                    let uu____15179 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15179  in
                  Prims.strcat uu____15177 uu____15178  in
                let uu____15180 =
                  let uu____15181 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15182 =
                    let uu____15183 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15183  in
                  Prims.strcat uu____15181 uu____15182  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15175
                  uu____15176 uu____15180
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15186,uu____15187) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15212,FStar_Syntax_Syntax.Tm_delayed uu____15213) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15238,uu____15239) ->
                  let uu____15266 =
                    let uu___188_15267 = problem  in
                    let uu____15268 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___188_15267.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15268;
                      FStar_TypeChecker_Common.relation =
                        (uu___188_15267.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___188_15267.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___188_15267.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___188_15267.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___188_15267.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___188_15267.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___188_15267.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___188_15267.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15266 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15269,uu____15270) ->
                  let uu____15277 =
                    let uu___189_15278 = problem  in
                    let uu____15279 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___189_15278.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15279;
                      FStar_TypeChecker_Common.relation =
                        (uu___189_15278.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___189_15278.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___189_15278.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___189_15278.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___189_15278.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___189_15278.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___189_15278.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___189_15278.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15277 wl
              | (uu____15280,FStar_Syntax_Syntax.Tm_ascribed uu____15281) ->
                  let uu____15308 =
                    let uu___190_15309 = problem  in
                    let uu____15310 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___190_15309.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___190_15309.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___190_15309.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15310;
                      FStar_TypeChecker_Common.element =
                        (uu___190_15309.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___190_15309.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___190_15309.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___190_15309.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___190_15309.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___190_15309.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15308 wl
              | (uu____15311,FStar_Syntax_Syntax.Tm_meta uu____15312) ->
                  let uu____15319 =
                    let uu___191_15320 = problem  in
                    let uu____15321 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___191_15320.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___191_15320.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___191_15320.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15321;
                      FStar_TypeChecker_Common.element =
                        (uu___191_15320.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___191_15320.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___191_15320.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___191_15320.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___191_15320.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___191_15320.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15319 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15323),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15325)) ->
                  let uu____15334 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15334
              | (FStar_Syntax_Syntax.Tm_bvar uu____15335,uu____15336) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15337,FStar_Syntax_Syntax.Tm_bvar uu____15338) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___146_15397 =
                    match uu___146_15397 with
                    | [] -> c
                    | bs ->
                        let uu____15419 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15419
                     in
                  let uu____15428 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15428 with
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
                                    let uu____15551 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15551
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
                  let mk_t t l uu___147_15626 =
                    match uu___147_15626 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15660 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15660 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____15779 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____15780 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____15779
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____15780 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____15781,uu____15782) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15809 -> true
                    | uu____15826 -> false  in
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
                      (let uu____15867 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___192_15875 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___192_15875.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___192_15875.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___192_15875.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___192_15875.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___192_15875.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___192_15875.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___192_15875.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___192_15875.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___192_15875.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___192_15875.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___192_15875.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___192_15875.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___192_15875.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___192_15875.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___192_15875.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___192_15875.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___192_15875.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___192_15875.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___192_15875.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___192_15875.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___192_15875.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___192_15875.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___192_15875.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___192_15875.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___192_15875.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___192_15875.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___192_15875.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___192_15875.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___192_15875.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___192_15875.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___192_15875.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___192_15875.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___192_15875.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___192_15875.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___192_15875.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15867 with
                       | (uu____15878,ty,uu____15880) ->
                           let uu____15881 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15881)
                     in
                  let uu____15882 =
                    let uu____15895 = maybe_eta t1  in
                    let uu____15900 = maybe_eta t2  in
                    (uu____15895, uu____15900)  in
                  (match uu____15882 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___193_15924 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___193_15924.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___193_15924.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___193_15924.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___193_15924.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___193_15924.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___193_15924.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___193_15924.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___193_15924.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15935 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15935
                       then
                         let uu____15936 = destruct_flex_t not_abs wl  in
                         (match uu____15936 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___194_15951 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___194_15951.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___194_15951.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___194_15951.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___194_15951.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___194_15951.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___194_15951.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___194_15951.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___194_15951.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____15963 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15963
                       then
                         let uu____15964 = destruct_flex_t not_abs wl  in
                         (match uu____15964 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___194_15979 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___194_15979.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___194_15979.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___194_15979.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___194_15979.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___194_15979.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___194_15979.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___194_15979.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___194_15979.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____15981 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____15994,FStar_Syntax_Syntax.Tm_abs uu____15995) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16022 -> true
                    | uu____16039 -> false  in
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
                      (let uu____16080 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___192_16088 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___192_16088.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___192_16088.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___192_16088.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___192_16088.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___192_16088.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___192_16088.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___192_16088.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___192_16088.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___192_16088.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___192_16088.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___192_16088.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___192_16088.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___192_16088.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___192_16088.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___192_16088.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___192_16088.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___192_16088.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___192_16088.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___192_16088.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___192_16088.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___192_16088.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___192_16088.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___192_16088.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___192_16088.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___192_16088.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___192_16088.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___192_16088.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___192_16088.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___192_16088.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___192_16088.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___192_16088.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___192_16088.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___192_16088.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___192_16088.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___192_16088.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16080 with
                       | (uu____16091,ty,uu____16093) ->
                           let uu____16094 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16094)
                     in
                  let uu____16095 =
                    let uu____16108 = maybe_eta t1  in
                    let uu____16113 = maybe_eta t2  in
                    (uu____16108, uu____16113)  in
                  (match uu____16095 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___193_16137 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___193_16137.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___193_16137.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___193_16137.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___193_16137.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___193_16137.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___193_16137.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___193_16137.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___193_16137.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16148 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16148
                       then
                         let uu____16149 = destruct_flex_t not_abs wl  in
                         (match uu____16149 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___194_16164 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___194_16164.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___194_16164.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___194_16164.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___194_16164.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___194_16164.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___194_16164.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___194_16164.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___194_16164.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16176 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16176
                       then
                         let uu____16177 = destruct_flex_t not_abs wl  in
                         (match uu____16177 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___194_16192 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___194_16192.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___194_16192.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___194_16192.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___194_16192.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___194_16192.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___194_16192.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___194_16192.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___194_16192.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16194 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16222 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16222) &&
                       (let uu____16226 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16226))
                      &&
                      (let uu____16233 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16233 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___148_16245 =
                             match uu___148_16245 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16246 -> true
                             | uu____16247 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16248 -> false)
                     in
                  let uu____16249 = as_refinement should_delta env wl t1  in
                  (match uu____16249 with
                   | (x11,phi1) ->
                       let uu____16256 = as_refinement should_delta env wl t2
                          in
                       (match uu____16256 with
                        | (x21,phi21) ->
                            let uu____16263 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16263 with
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
                                   let uu____16329 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16329
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16341 =
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
                                   let uu____16352 =
                                     let uu____16357 =
                                       let uu____16364 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16364]  in
                                     mk_t_problem wl1 uu____16357 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16352 with
                                    | (ref_prob,wl2) ->
                                        let uu____16379 =
                                          solve env1
                                            (let uu___195_16381 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___195_16381.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___195_16381.smt_ok);
                                               tcenv = (uu___195_16381.tcenv);
                                               wl_implicits =
                                                 (uu___195_16381.wl_implicits)
                                             })
                                           in
                                        (match uu____16379 with
                                         | Failed uu____16388 -> fallback ()
                                         | Success uu____16393 ->
                                             let guard =
                                               let uu____16401 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16401
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___196_16410 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___196_16410.attempting);
                                                 wl_deferred =
                                                   (uu___196_16410.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___196_16410.defer_ok);
                                                 smt_ok =
                                                   (uu___196_16410.smt_ok);
                                                 tcenv =
                                                   (uu___196_16410.tcenv);
                                                 wl_implicits =
                                                   (uu___196_16410.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16412,FStar_Syntax_Syntax.Tm_uvar uu____16413) ->
                  let uu____16442 = destruct_flex_t t1 wl  in
                  (match uu____16442 with
                   | (f1,wl1) ->
                       let uu____16449 = destruct_flex_t t2 wl1  in
                       (match uu____16449 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16456;
                    FStar_Syntax_Syntax.pos = uu____16457;
                    FStar_Syntax_Syntax.vars = uu____16458;_},uu____16459),FStar_Syntax_Syntax.Tm_uvar
                 uu____16460) ->
                  let uu____16509 = destruct_flex_t t1 wl  in
                  (match uu____16509 with
                   | (f1,wl1) ->
                       let uu____16516 = destruct_flex_t t2 wl1  in
                       (match uu____16516 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16523,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16524;
                    FStar_Syntax_Syntax.pos = uu____16525;
                    FStar_Syntax_Syntax.vars = uu____16526;_},uu____16527))
                  ->
                  let uu____16576 = destruct_flex_t t1 wl  in
                  (match uu____16576 with
                   | (f1,wl1) ->
                       let uu____16583 = destruct_flex_t t2 wl1  in
                       (match uu____16583 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16590;
                    FStar_Syntax_Syntax.pos = uu____16591;
                    FStar_Syntax_Syntax.vars = uu____16592;_},uu____16593),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16594;
                    FStar_Syntax_Syntax.pos = uu____16595;
                    FStar_Syntax_Syntax.vars = uu____16596;_},uu____16597))
                  ->
                  let uu____16666 = destruct_flex_t t1 wl  in
                  (match uu____16666 with
                   | (f1,wl1) ->
                       let uu____16673 = destruct_flex_t t2 wl1  in
                       (match uu____16673 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16680,uu____16681) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16696 = destruct_flex_t t1 wl  in
                  (match uu____16696 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16703;
                    FStar_Syntax_Syntax.pos = uu____16704;
                    FStar_Syntax_Syntax.vars = uu____16705;_},uu____16706),uu____16707)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16742 = destruct_flex_t t1 wl  in
                  (match uu____16742 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____16749,FStar_Syntax_Syntax.Tm_uvar uu____16750) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____16765,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16766;
                    FStar_Syntax_Syntax.pos = uu____16767;
                    FStar_Syntax_Syntax.vars = uu____16768;_},uu____16769))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16804,FStar_Syntax_Syntax.Tm_arrow uu____16805) ->
                  solve_t' env
                    (let uu___197_16833 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16833.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___197_16833.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16833.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16833.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16833.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___197_16833.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16833.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16833.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16833.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16834;
                    FStar_Syntax_Syntax.pos = uu____16835;
                    FStar_Syntax_Syntax.vars = uu____16836;_},uu____16837),FStar_Syntax_Syntax.Tm_arrow
                 uu____16838) ->
                  solve_t' env
                    (let uu___197_16886 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_16886.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___197_16886.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_16886.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_16886.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_16886.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___197_16886.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_16886.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_16886.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_16886.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____16887,FStar_Syntax_Syntax.Tm_uvar uu____16888) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____16903,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16904;
                    FStar_Syntax_Syntax.pos = uu____16905;
                    FStar_Syntax_Syntax.vars = uu____16906;_},uu____16907))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____16942,uu____16943) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16958;
                    FStar_Syntax_Syntax.pos = uu____16959;
                    FStar_Syntax_Syntax.vars = uu____16960;_},uu____16961),uu____16962)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____16997,uu____16998) ->
                  let t21 =
                    let uu____17006 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17006  in
                  solve_t env
                    (let uu___198_17032 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_17032.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_17032.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___198_17032.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___198_17032.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_17032.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___198_17032.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_17032.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_17032.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_17032.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17033,FStar_Syntax_Syntax.Tm_refine uu____17034) ->
                  let t11 =
                    let uu____17042 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17042  in
                  solve_t env
                    (let uu___199_17068 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___199_17068.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___199_17068.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___199_17068.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___199_17068.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___199_17068.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___199_17068.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___199_17068.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___199_17068.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___199_17068.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____17145 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____17145 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____17366 = br1  in
                             (match uu____17366 with
                              | (p1,w1,uu____17391) ->
                                  let uu____17408 = br2  in
                                  (match uu____17408 with
                                   | (p2,w2,uu____17427) ->
                                       let uu____17432 =
                                         let uu____17433 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____17433  in
                                       if uu____17432
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____17449 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____17449 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____17482 = br2  in
                                              (match uu____17482 with
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
                                                     let uu____17517 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____17517
                                                      in
                                                   let uu____17528 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____17551,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____17568) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____17611 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____17611
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____17528
                                                     (fun uu____17653  ->
                                                        match uu____17653
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____17674 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____17674
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____17689
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____17689
                                                                   (fun
                                                                    uu____17713
                                                                     ->
                                                                    match uu____17713
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
                         | uu____17798 -> FStar_Pervasives_Native.None  in
                       let uu____17835 = solve_branches wl1 brs1 brs2  in
                       (match uu____17835 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____17866,uu____17867) ->
                  let head1 =
                    let uu____17891 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17891
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17931 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17931
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17971 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____17971
                    then
                      let uu____17972 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17973 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17974 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17972 uu____17973 uu____17974
                    else ());
                   (let uu____17976 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17976
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17983 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17983
                       then
                         let uu____17984 =
                           let uu____17991 =
                             let uu____17992 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17992 = FStar_Syntax_Util.Equal  in
                           if uu____17991
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18002 = mk_eq2 wl orig t1 t2  in
                              match uu____18002 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17984 with
                         | (guard,wl1) ->
                             let uu____18023 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18023
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18026,uu____18027) ->
                  let head1 =
                    let uu____18035 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18035
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18075 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18075
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18115 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18115
                    then
                      let uu____18116 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18117 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18118 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18116 uu____18117 uu____18118
                    else ());
                   (let uu____18120 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18120
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18127 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18127
                       then
                         let uu____18128 =
                           let uu____18135 =
                             let uu____18136 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18136 = FStar_Syntax_Util.Equal  in
                           if uu____18135
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18146 = mk_eq2 wl orig t1 t2  in
                              match uu____18146 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18128 with
                         | (guard,wl1) ->
                             let uu____18167 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18167
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18170,uu____18171) ->
                  let head1 =
                    let uu____18173 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18173
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18213 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18213
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18253 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18253
                    then
                      let uu____18254 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18255 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18256 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18254 uu____18255 uu____18256
                    else ());
                   (let uu____18258 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18258
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18265 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18265
                       then
                         let uu____18266 =
                           let uu____18273 =
                             let uu____18274 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18274 = FStar_Syntax_Util.Equal  in
                           if uu____18273
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18284 = mk_eq2 wl orig t1 t2  in
                              match uu____18284 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18266 with
                         | (guard,wl1) ->
                             let uu____18305 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18305
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18308,uu____18309) ->
                  let head1 =
                    let uu____18311 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18311
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18351 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18351
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18391 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18391
                    then
                      let uu____18392 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18393 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18394 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18392 uu____18393 uu____18394
                    else ());
                   (let uu____18396 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18396
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18403 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18403
                       then
                         let uu____18404 =
                           let uu____18411 =
                             let uu____18412 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18412 = FStar_Syntax_Util.Equal  in
                           if uu____18411
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18422 = mk_eq2 wl orig t1 t2  in
                              match uu____18422 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18404 with
                         | (guard,wl1) ->
                             let uu____18443 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18443
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18446,uu____18447) ->
                  let head1 =
                    let uu____18449 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18449
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18489 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18489
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18529 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18529
                    then
                      let uu____18530 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18531 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18532 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18530 uu____18531 uu____18532
                    else ());
                   (let uu____18534 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18534
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18541 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18541
                       then
                         let uu____18542 =
                           let uu____18549 =
                             let uu____18550 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18550 = FStar_Syntax_Util.Equal  in
                           if uu____18549
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18560 = mk_eq2 wl orig t1 t2  in
                              match uu____18560 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18542 with
                         | (guard,wl1) ->
                             let uu____18581 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18581
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____18584,uu____18585) ->
                  let head1 =
                    let uu____18601 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18601
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18641 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18641
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18681 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18681
                    then
                      let uu____18682 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18683 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18684 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18682 uu____18683 uu____18684
                    else ());
                   (let uu____18686 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18686
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18693 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18693
                       then
                         let uu____18694 =
                           let uu____18701 =
                             let uu____18702 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18702 = FStar_Syntax_Util.Equal  in
                           if uu____18701
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18712 = mk_eq2 wl orig t1 t2  in
                              match uu____18712 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18694 with
                         | (guard,wl1) ->
                             let uu____18733 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18733
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18736,FStar_Syntax_Syntax.Tm_match uu____18737) ->
                  let head1 =
                    let uu____18761 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18761
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18801 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18801
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18841 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18841
                    then
                      let uu____18842 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18843 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18844 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18842 uu____18843 uu____18844
                    else ());
                   (let uu____18846 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18846
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18853 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18853
                       then
                         let uu____18854 =
                           let uu____18861 =
                             let uu____18862 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18862 = FStar_Syntax_Util.Equal  in
                           if uu____18861
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18872 = mk_eq2 wl orig t1 t2  in
                              match uu____18872 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18854 with
                         | (guard,wl1) ->
                             let uu____18893 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18893
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18896,FStar_Syntax_Syntax.Tm_uinst uu____18897) ->
                  let head1 =
                    let uu____18905 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18905
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18945 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18945
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18985 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18985
                    then
                      let uu____18986 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18987 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18988 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18986 uu____18987 uu____18988
                    else ());
                   (let uu____18990 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18990
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18997 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18997
                       then
                         let uu____18998 =
                           let uu____19005 =
                             let uu____19006 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19006 = FStar_Syntax_Util.Equal  in
                           if uu____19005
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19016 = mk_eq2 wl orig t1 t2  in
                              match uu____19016 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18998 with
                         | (guard,wl1) ->
                             let uu____19037 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19037
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19040,FStar_Syntax_Syntax.Tm_name uu____19041) ->
                  let head1 =
                    let uu____19043 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19043
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19083 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19083
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19123 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19123
                    then
                      let uu____19124 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19125 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19126 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19124 uu____19125 uu____19126
                    else ());
                   (let uu____19128 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19128
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19135 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19135
                       then
                         let uu____19136 =
                           let uu____19143 =
                             let uu____19144 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19144 = FStar_Syntax_Util.Equal  in
                           if uu____19143
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19154 = mk_eq2 wl orig t1 t2  in
                              match uu____19154 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19136 with
                         | (guard,wl1) ->
                             let uu____19175 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19175
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19178,FStar_Syntax_Syntax.Tm_constant uu____19179) ->
                  let head1 =
                    let uu____19181 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19181
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19221 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19221
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19261 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19261
                    then
                      let uu____19262 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19263 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19264 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19262 uu____19263 uu____19264
                    else ());
                   (let uu____19266 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19266
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19273 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19273
                       then
                         let uu____19274 =
                           let uu____19281 =
                             let uu____19282 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19282 = FStar_Syntax_Util.Equal  in
                           if uu____19281
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19292 = mk_eq2 wl orig t1 t2  in
                              match uu____19292 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19274 with
                         | (guard,wl1) ->
                             let uu____19313 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19313
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19316,FStar_Syntax_Syntax.Tm_fvar uu____19317) ->
                  let head1 =
                    let uu____19319 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19319
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19359 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19359
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19399 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19399
                    then
                      let uu____19400 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19401 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19402 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19400 uu____19401 uu____19402
                    else ());
                   (let uu____19404 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19404
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19411 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19411
                       then
                         let uu____19412 =
                           let uu____19419 =
                             let uu____19420 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19420 = FStar_Syntax_Util.Equal  in
                           if uu____19419
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19430 = mk_eq2 wl orig t1 t2  in
                              match uu____19430 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19412 with
                         | (guard,wl1) ->
                             let uu____19451 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19451
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19454,FStar_Syntax_Syntax.Tm_app uu____19455) ->
                  let head1 =
                    let uu____19471 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19471
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19511 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19511
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19551 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19551
                    then
                      let uu____19552 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19553 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19554 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19552 uu____19553 uu____19554
                    else ());
                   (let uu____19556 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19556
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19563 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19563
                       then
                         let uu____19564 =
                           let uu____19571 =
                             let uu____19572 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19572 = FStar_Syntax_Util.Equal  in
                           if uu____19571
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19582 = mk_eq2 wl orig t1 t2  in
                              match uu____19582 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19564 with
                         | (guard,wl1) ->
                             let uu____19603 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19603
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____19606,FStar_Syntax_Syntax.Tm_let uu____19607) ->
                  let uu____19632 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____19632
                  then
                    let uu____19633 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____19633
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____19635,uu____19636) ->
                  let uu____19649 =
                    let uu____19654 =
                      let uu____19655 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19656 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19657 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19658 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19655 uu____19656 uu____19657 uu____19658
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19654)
                     in
                  FStar_Errors.raise_error uu____19649
                    t1.FStar_Syntax_Syntax.pos
              | (uu____19659,FStar_Syntax_Syntax.Tm_let uu____19660) ->
                  let uu____19673 =
                    let uu____19678 =
                      let uu____19679 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19680 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19681 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19682 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19679 uu____19680 uu____19681 uu____19682
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19678)
                     in
                  FStar_Errors.raise_error uu____19673
                    t1.FStar_Syntax_Syntax.pos
              | uu____19683 -> giveup env "head tag mismatch" orig))))

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
          (let uu____19742 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____19742
           then
             let uu____19743 =
               let uu____19744 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____19744  in
             let uu____19745 =
               let uu____19746 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____19746  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____19743 uu____19745
           else ());
          (let uu____19748 =
             let uu____19749 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____19749  in
           if uu____19748
           then
             let uu____19750 =
               let uu____19751 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____19752 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____19751 uu____19752
                in
             giveup env uu____19750 orig
           else
             (let uu____19754 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____19754 with
              | (ret_sub_prob,wl1) ->
                  let uu____19761 =
                    FStar_List.fold_right2
                      (fun uu____19794  ->
                         fun uu____19795  ->
                           fun uu____19796  ->
                             match (uu____19794, uu____19795, uu____19796)
                             with
                             | ((a1,uu____19832),(a2,uu____19834),(arg_sub_probs,wl2))
                                 ->
                                 let uu____19855 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____19855 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____19761 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____19884 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____19884  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____19914 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____19917)::[] -> wp1
              | uu____19934 ->
                  let uu____19943 =
                    let uu____19944 =
                      let uu____19945 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____19945  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____19944
                     in
                  failwith uu____19943
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____19951 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____19951]
              | x -> x  in
            let uu____19953 =
              let uu____19962 =
                let uu____19969 =
                  let uu____19970 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____19970 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____19969  in
              [uu____19962]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____19953;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____19983 = lift_c1 ()  in solve_eq uu____19983 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___149_19989  ->
                       match uu___149_19989 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____19990 -> false))
                in
             let uu____19991 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20017)::uu____20018,(wp2,uu____20020)::uu____20021)
                   -> (wp1, wp2)
               | uu____20074 ->
                   let uu____20095 =
                     let uu____20100 =
                       let uu____20101 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20102 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20101 uu____20102
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20100)
                      in
                   FStar_Errors.raise_error uu____20095
                     env.FStar_TypeChecker_Env.range
                in
             match uu____19991 with
             | (wpc1,wpc2) ->
                 let uu____20109 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20109
                 then
                   let uu____20112 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20112 wl
                 else
                   (let uu____20114 =
                      let uu____20121 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20121  in
                    match uu____20114 with
                    | (c2_decl,qualifiers) ->
                        let uu____20142 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20142
                        then
                          let c1_repr =
                            let uu____20146 =
                              let uu____20147 =
                                let uu____20148 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20148  in
                              let uu____20149 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20147 uu____20149
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20146
                             in
                          let c2_repr =
                            let uu____20151 =
                              let uu____20152 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20153 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20152 uu____20153
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20151
                             in
                          let uu____20154 =
                            let uu____20159 =
                              let uu____20160 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20161 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20160 uu____20161
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20159
                             in
                          (match uu____20154 with
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
                                 ((let uu____20175 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20175
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20178 =
                                     let uu____20185 =
                                       let uu____20186 =
                                         let uu____20201 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20204 =
                                           let uu____20213 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20220 =
                                             let uu____20229 =
                                               let uu____20236 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20236
                                                in
                                             [uu____20229]  in
                                           uu____20213 :: uu____20220  in
                                         (uu____20201, uu____20204)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20186
                                        in
                                     FStar_Syntax_Syntax.mk uu____20185  in
                                   uu____20178 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20271 =
                                    let uu____20278 =
                                      let uu____20279 =
                                        let uu____20294 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20297 =
                                          let uu____20306 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20313 =
                                            let uu____20322 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20329 =
                                              let uu____20338 =
                                                let uu____20345 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20345
                                                 in
                                              [uu____20338]  in
                                            uu____20322 :: uu____20329  in
                                          uu____20306 :: uu____20313  in
                                        (uu____20294, uu____20297)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20279
                                       in
                                    FStar_Syntax_Syntax.mk uu____20278  in
                                  uu____20271 FStar_Pervasives_Native.None r)
                              in
                           let uu____20383 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20383 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20391 =
                                   let uu____20394 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____20394
                                    in
                                 solve_prob orig uu____20391 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____20401 = FStar_Util.physical_equality c1 c2  in
        if uu____20401
        then
          let uu____20402 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20402
        else
          ((let uu____20405 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20405
            then
              let uu____20406 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20407 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20406
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20407
            else ());
           (let uu____20409 =
              let uu____20418 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20421 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20418, uu____20421)  in
            match uu____20409 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20439),FStar_Syntax_Syntax.Total
                    (t2,uu____20441)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20458 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20458 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20459,FStar_Syntax_Syntax.Total uu____20460) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20478),FStar_Syntax_Syntax.Total
                    (t2,uu____20480)) ->
                     let uu____20497 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20497 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20499),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20501)) ->
                     let uu____20518 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20518 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20520),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20522)) ->
                     let uu____20539 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20539 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20540,FStar_Syntax_Syntax.Comp uu____20541) ->
                     let uu____20550 =
                       let uu___200_20553 = problem  in
                       let uu____20556 =
                         let uu____20557 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20557
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_20553.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20556;
                         FStar_TypeChecker_Common.relation =
                           (uu___200_20553.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___200_20553.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___200_20553.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_20553.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_20553.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_20553.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_20553.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_20553.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20550 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20558,FStar_Syntax_Syntax.Comp uu____20559) ->
                     let uu____20568 =
                       let uu___200_20571 = problem  in
                       let uu____20574 =
                         let uu____20575 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20575
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_20571.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20574;
                         FStar_TypeChecker_Common.relation =
                           (uu___200_20571.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___200_20571.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___200_20571.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_20571.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_20571.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_20571.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_20571.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_20571.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20568 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20576,FStar_Syntax_Syntax.GTotal uu____20577) ->
                     let uu____20586 =
                       let uu___201_20589 = problem  in
                       let uu____20592 =
                         let uu____20593 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20593
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20589.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___201_20589.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20589.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20592;
                         FStar_TypeChecker_Common.element =
                           (uu___201_20589.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20589.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20589.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20589.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20589.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20589.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20586 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20594,FStar_Syntax_Syntax.Total uu____20595) ->
                     let uu____20604 =
                       let uu___201_20607 = problem  in
                       let uu____20610 =
                         let uu____20611 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20611
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20607.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___201_20607.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20607.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20610;
                         FStar_TypeChecker_Common.element =
                           (uu___201_20607.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20607.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20607.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20607.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20607.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20607.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20604 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20612,FStar_Syntax_Syntax.Comp uu____20613) ->
                     let uu____20614 =
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
                     if uu____20614
                     then
                       let uu____20615 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____20615 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20619 =
                            let uu____20624 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____20624
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20630 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____20631 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____20630, uu____20631))
                             in
                          match uu____20619 with
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
                           (let uu____20638 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____20638
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20640 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____20640 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20643 =
                                  let uu____20644 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____20645 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____20644 uu____20645
                                   in
                                giveup env uu____20643 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____20652 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20685  ->
              match uu____20685 with
              | (uu____20696,tm,uu____20698,uu____20699,uu____20700) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____20652 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____20733 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____20733 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____20751 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____20779  ->
                match uu____20779 with
                | (u1,u2) ->
                    let uu____20786 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____20787 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____20786 uu____20787))
         in
      FStar_All.pipe_right uu____20751 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____20814,[])) -> "{}"
      | uu____20839 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____20862 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____20862
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____20865 =
              FStar_List.map
                (fun uu____20875  ->
                   match uu____20875 with
                   | (uu____20880,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____20865 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____20885 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____20885 imps
  
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
                  let uu____20938 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____20938
                  then
                    let uu____20939 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____20940 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____20939
                      (rel_to_string rel) uu____20940
                  else "TOP"  in
                let uu____20942 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____20942 with
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
              let uu____20999 =
                let uu____21002 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____21002
                 in
              FStar_Syntax_Syntax.new_bv uu____20999 t1  in
            let uu____21005 =
              let uu____21010 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21010
               in
            match uu____21005 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____21066 = FStar_Options.eager_inference ()  in
          if uu____21066
          then
            let uu___202_21067 = probs  in
            {
              attempting = (uu___202_21067.attempting);
              wl_deferred = (uu___202_21067.wl_deferred);
              ctr = (uu___202_21067.ctr);
              defer_ok = false;
              smt_ok = (uu___202_21067.smt_ok);
              tcenv = (uu___202_21067.tcenv);
              wl_implicits = (uu___202_21067.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21087 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21087
              then
                let uu____21088 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21088
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
          ((let uu____21110 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21110
            then
              let uu____21111 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21111
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21115 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21115
             then
               let uu____21116 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21116
             else ());
            (let f2 =
               let uu____21119 =
                 let uu____21120 = FStar_Syntax_Util.unmeta f1  in
                 uu____21120.FStar_Syntax_Syntax.n  in
               match uu____21119 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21124 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___203_21125 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___203_21125.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___203_21125.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___203_21125.FStar_TypeChecker_Env.implicits)
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
            let uu____21239 =
              let uu____21240 =
                let uu____21241 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21241;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21240  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____21239
  
let with_guard_no_simp :
  'Auu____21256 .
    'Auu____21256 ->
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
            let uu____21279 =
              let uu____21280 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21280;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21279
  
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
          (let uu____21320 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21320
           then
             let uu____21321 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21322 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21321
               uu____21322
           else ());
          (let uu____21324 =
             let uu____21329 = empty_worklist env  in
             let uu____21330 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____21329 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____21330
              in
           match uu____21324 with
           | (prob,wl) ->
               let g =
                 let uu____21338 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21358  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21338  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21402 = try_teq true env t1 t2  in
        match uu____21402 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21406 = FStar_TypeChecker_Env.get_range env  in
              let uu____21407 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21406 uu____21407);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21414 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21414
              then
                let uu____21415 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21416 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21417 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21415
                  uu____21416 uu____21417
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
          let uu____21439 = FStar_TypeChecker_Env.get_range env  in
          let uu____21440 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21439 uu____21440
  
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
        (let uu____21465 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21465
         then
           let uu____21466 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21467 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21466 uu____21467
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21470 =
           let uu____21477 = empty_worklist env  in
           let uu____21478 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____21477 env c1 rel c2 FStar_Pervasives_Native.None
             uu____21478 "sub_comp"
            in
         match uu____21470 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21488 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21508  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21488)
  
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
      fun uu____21563  ->
        match uu____21563 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21606 =
                 let uu____21611 =
                   let uu____21612 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21613 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21612 uu____21613
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21611)  in
               let uu____21614 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21606 uu____21614)
               in
            let equiv1 v1 v' =
              let uu____21626 =
                let uu____21631 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21632 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21631, uu____21632)  in
              match uu____21626 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21651 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21681 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____21681 with
                      | FStar_Syntax_Syntax.U_unif uu____21688 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21717  ->
                                    match uu____21717 with
                                    | (u,v') ->
                                        let uu____21726 = equiv1 v1 v'  in
                                        if uu____21726
                                        then
                                          let uu____21729 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____21729 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____21745 -> []))
               in
            let uu____21750 =
              let wl =
                let uu___204_21754 = empty_worklist env  in
                {
                  attempting = (uu___204_21754.attempting);
                  wl_deferred = (uu___204_21754.wl_deferred);
                  ctr = (uu___204_21754.ctr);
                  defer_ok = false;
                  smt_ok = (uu___204_21754.smt_ok);
                  tcenv = (uu___204_21754.tcenv);
                  wl_implicits = (uu___204_21754.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21772  ->
                      match uu____21772 with
                      | (lb,v1) ->
                          let uu____21779 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____21779 with
                           | USolved wl1 -> ()
                           | uu____21781 -> fail1 lb v1)))
               in
            let rec check_ineq uu____21791 =
              match uu____21791 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21800) -> true
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
                      uu____21823,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21825,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21836) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21843,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21851 -> false)
               in
            let uu____21856 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21871  ->
                      match uu____21871 with
                      | (u,v1) ->
                          let uu____21878 = check_ineq (u, v1)  in
                          if uu____21878
                          then true
                          else
                            ((let uu____21881 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____21881
                              then
                                let uu____21882 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____21883 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____21882
                                  uu____21883
                              else ());
                             false)))
               in
            if uu____21856
            then ()
            else
              ((let uu____21887 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____21887
                then
                  ((let uu____21889 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21889);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21899 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21899))
                else ());
               (let uu____21909 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____21909))
  
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
        let fail1 uu____21976 =
          match uu____21976 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___205_21997 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___205_21997.attempting);
            wl_deferred = (uu___205_21997.wl_deferred);
            ctr = (uu___205_21997.ctr);
            defer_ok;
            smt_ok = (uu___205_21997.smt_ok);
            tcenv = (uu___205_21997.tcenv);
            wl_implicits = (uu___205_21997.wl_implicits)
          }  in
        (let uu____21999 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21999
         then
           let uu____22000 = FStar_Util.string_of_bool defer_ok  in
           let uu____22001 = wl_to_string wl  in
           let uu____22002 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22000 uu____22001 uu____22002
         else ());
        (let g1 =
           let uu____22015 = solve_and_commit env wl fail1  in
           match uu____22015 with
           | FStar_Pervasives_Native.Some
               (uu____22022::uu____22023,uu____22024) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___206_22049 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___206_22049.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___206_22049.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22060 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___207_22068 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___207_22068.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___207_22068.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___207_22068.FStar_TypeChecker_Env.implicits)
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
    let uu____22116 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22116 with
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
            let uu___208_22239 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___208_22239.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___208_22239.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___208_22239.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22240 =
            let uu____22241 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22241  in
          if uu____22240
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22249 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22250 =
                       let uu____22251 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22251
                        in
                     FStar_Errors.diag uu____22249 uu____22250)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22255 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22256 =
                        let uu____22257 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22257
                         in
                      FStar_Errors.diag uu____22255 uu____22256)
                   else ();
                   (let uu____22260 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22260 "discharge_guard'"
                      env vc1);
                   (let uu____22261 = check_trivial vc1  in
                    match uu____22261 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22268 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22269 =
                                let uu____22270 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22270
                                 in
                              FStar_Errors.diag uu____22268 uu____22269)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22275 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22276 =
                                let uu____22277 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22277
                                 in
                              FStar_Errors.diag uu____22275 uu____22276)
                           else ();
                           (let vcs =
                              let uu____22290 = FStar_Options.use_tactics ()
                                 in
                              if uu____22290
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22312  ->
                                     (let uu____22314 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____22314);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22357  ->
                                              match uu____22357 with
                                              | (env1,goal,opts) ->
                                                  let uu____22373 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22373, opts)))))
                              else
                                (let uu____22375 =
                                   let uu____22382 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22382)  in
                                 [uu____22375])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22419  ->
                                    match uu____22419 with
                                    | (env1,goal,opts) ->
                                        let uu____22435 = check_trivial goal
                                           in
                                        (match uu____22435 with
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
                                                (let uu____22443 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22444 =
                                                   let uu____22445 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22446 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22445 uu____22446
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22443 uu____22444)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22449 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22450 =
                                                   let uu____22451 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22451
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22449 uu____22450)
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
      let uu____22465 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22465 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22472 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22472
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22483 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22483 with
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
            let uu____22516 = FStar_Syntax_Util.head_and_args u  in
            match uu____22516 with
            | (hd1,uu____22532) ->
                let uu____22553 =
                  let uu____22554 = FStar_Syntax_Subst.compress u  in
                  uu____22554.FStar_Syntax_Syntax.n  in
                (match uu____22553 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____22557 -> true
                 | uu____22572 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____22592 = acc  in
            match uu____22592 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22654 = hd1  in
                     (match uu____22654 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____22671 = unresolved tm  in
                             if uu____22671
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___209_22684 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___209_22684.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___209_22684.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___209_22684.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___209_22684.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___209_22684.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___209_22684.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___209_22684.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___209_22684.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___209_22684.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___209_22684.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___209_22684.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___209_22684.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___209_22684.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___209_22684.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___209_22684.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___209_22684.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___209_22684.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___209_22684.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___209_22684.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___209_22684.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___209_22684.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___209_22684.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___209_22684.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___209_22684.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___209_22684.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___209_22684.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___209_22684.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___209_22684.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___209_22684.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___209_22684.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___209_22684.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___209_22684.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___209_22684.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___209_22684.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___209_22684.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___209_22684.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___209_22684.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___210_22687 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___210_22687.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___210_22687.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___210_22687.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___210_22687.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___210_22687.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___210_22687.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___210_22687.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___210_22687.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___210_22687.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___210_22687.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___210_22687.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___210_22687.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___210_22687.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___210_22687.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___210_22687.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___210_22687.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___210_22687.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___210_22687.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___210_22687.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___210_22687.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___210_22687.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___210_22687.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___210_22687.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___210_22687.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___210_22687.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___210_22687.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___210_22687.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___210_22687.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___210_22687.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___210_22687.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___210_22687.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___210_22687.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___210_22687.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___210_22687.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___210_22687.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___210_22687.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___210_22687.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____22690 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____22690
                                 then
                                   let uu____22691 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____22692 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____22693 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____22694 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____22691 uu____22692 uu____22693
                                     reason uu____22694
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e when FStar_Errors.handleable e ->
                                       ((let uu____22705 =
                                           let uu____22714 =
                                             let uu____22721 =
                                               let uu____22722 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____22723 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____22722 uu____22723
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____22721, r)
                                              in
                                           [uu____22714]  in
                                         FStar_Errors.add_errors uu____22705);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___213_22737 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___213_22737.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___213_22737.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___213_22737.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____22740 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____22747  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____22740 with
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
          let uu___214_22759 = g  in
          let uu____22760 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___214_22759.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___214_22759.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___214_22759.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____22760
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
        let uu____22814 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____22814 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22825 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____22825
      | (reason,e,ctx_u,r,should_check)::uu____22831 ->
          let uu____22854 =
            let uu____22859 =
              let uu____22860 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____22861 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____22862 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____22860 uu____22861 reason uu____22862
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____22859)
             in
          FStar_Errors.raise_error uu____22854 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___215_22873 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___215_22873.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___215_22873.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___215_22873.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____22888 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22888 with
      | FStar_Pervasives_Native.Some uu____22894 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22910 = try_teq false env t1 t2  in
        match uu____22910 with
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
        (let uu____22944 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22944
         then
           let uu____22945 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____22946 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22945
             uu____22946
         else ());
        (let uu____22948 =
           let uu____22955 = empty_worklist env  in
           new_t_prob uu____22955 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____22948 with
         | (prob,x,wl) ->
             let g =
               let uu____22968 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____22988  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____22968  in
             ((let uu____23018 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23018
               then
                 let uu____23019 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23020 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23021 =
                   let uu____23022 = FStar_Util.must g  in
                   guard_to_string env uu____23022  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23019 uu____23020 uu____23021
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
        let uu____23056 = check_subtyping env t1 t2  in
        match uu____23056 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23075 =
              let uu____23076 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23076 g  in
            FStar_Pervasives_Native.Some uu____23075
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23094 = check_subtyping env t1 t2  in
        match uu____23094 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23113 =
              let uu____23114 =
                let uu____23115 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23115]  in
              close_guard env uu____23114 g  in
            FStar_Pervasives_Native.Some uu____23113
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23144 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23144
         then
           let uu____23145 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23146 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23145
             uu____23146
         else ());
        (let uu____23148 =
           let uu____23155 = empty_worklist env  in
           new_t_prob uu____23155 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23148 with
         | (prob,x,wl) ->
             let g =
               let uu____23162 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23182  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23162  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23213 =
                      let uu____23214 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23214]  in
                    close_guard env uu____23213 g1  in
                  discharge_guard_nosmt env g2))
  