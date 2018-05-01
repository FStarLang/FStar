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
          let uu___144_102 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___144_102.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___144_102.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___144_102.FStar_TypeChecker_Env.implicits)
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
          let uu___145_248 = g  in
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
              (uu___145_248.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___145_248.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___145_248.FStar_TypeChecker_Env.implicits)
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
          let uu___146_331 = g  in
          let uu____332 =
            let uu____333 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____333  in
          {
            FStar_TypeChecker_Env.guard_f = uu____332;
            FStar_TypeChecker_Env.deferred =
              (uu___146_331.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___146_331.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___146_331.FStar_TypeChecker_Env.implicits)
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
            let uu___147_499 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___147_499.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___147_499.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___147_499.FStar_TypeChecker_Env.implicits)
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
            let uu___148_559 = g  in
            let uu____560 =
              let uu____561 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____561  in
            {
              FStar_TypeChecker_Env.guard_f = uu____560;
              FStar_TypeChecker_Env.deferred =
                (uu___148_559.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___148_559.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___148_559.FStar_TypeChecker_Env.implicits)
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
                   (let uu___149_923 = wl  in
                    {
                      attempting = (uu___149_923.attempting);
                      wl_deferred = (uu___149_923.wl_deferred);
                      ctr = (uu___149_923.ctr);
                      defer_ok = (uu___149_923.defer_ok);
                      smt_ok = (uu___149_923.smt_ok);
                      tcenv = (uu___149_923.tcenv);
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
  fun uu___115_1069  ->
    match uu___115_1069 with
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
    fun uu___116_1116  ->
      match uu___116_1116 with
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
    fun uu___117_1150  ->
      match uu___117_1150 with
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
        let uu___150_1292 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___150_1292.wl_deferred);
          ctr = (uu___150_1292.ctr);
          defer_ok = (uu___150_1292.defer_ok);
          smt_ok;
          tcenv = (uu___150_1292.tcenv);
          wl_implicits = (uu___150_1292.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1299 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1299,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___151_1322 = empty_worklist env  in
      let uu____1323 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1323;
        wl_deferred = (uu___151_1322.wl_deferred);
        ctr = (uu___151_1322.ctr);
        defer_ok = (uu___151_1322.defer_ok);
        smt_ok = (uu___151_1322.smt_ok);
        tcenv = (uu___151_1322.tcenv);
        wl_implicits = (uu___151_1322.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___152_1343 = wl  in
        {
          attempting = (uu___152_1343.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___152_1343.ctr);
          defer_ok = (uu___152_1343.defer_ok);
          smt_ok = (uu___152_1343.smt_ok);
          tcenv = (uu___152_1343.tcenv);
          wl_implicits = (uu___152_1343.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___153_1364 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___153_1364.wl_deferred);
        ctr = (uu___153_1364.ctr);
        defer_ok = (uu___153_1364.defer_ok);
        smt_ok = (uu___153_1364.smt_ok);
        tcenv = (uu___153_1364.tcenv);
        wl_implicits = (uu___153_1364.wl_implicits)
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
  fun uu___118_1388  ->
    match uu___118_1388 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1393 .
    'Auu____1393 FStar_TypeChecker_Common.problem ->
      'Auu____1393 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___154_1405 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___154_1405.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___154_1405.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___154_1405.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___154_1405.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___154_1405.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___154_1405.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___154_1405.FStar_TypeChecker_Common.rank)
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
  fun uu___119_1429  ->
    match uu___119_1429 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___120_1444  ->
    match uu___120_1444 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___155_1450 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___155_1450.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___155_1450.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___155_1450.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___155_1450.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___155_1450.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___155_1450.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___155_1450.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___155_1450.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___155_1450.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___156_1458 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___156_1458.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___156_1458.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___156_1458.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___156_1458.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___156_1458.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___156_1458.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___156_1458.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___156_1458.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___156_1458.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___121_1470  ->
      match uu___121_1470 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___122_1475  ->
    match uu___122_1475 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___123_1486  ->
    match uu___123_1486 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___124_1499  ->
    match uu___124_1499 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___125_1512  ->
    match uu___125_1512 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___126_1523  ->
    match uu___126_1523 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___127_1538  ->
    match uu___127_1538 with
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
  fun uu___128_1813  ->
    match uu___128_1813 with
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
                          (let uu___157_2430 = wl  in
                           {
                             attempting = (uu___157_2430.attempting);
                             wl_deferred = (uu___157_2430.wl_deferred);
                             ctr = (uu___157_2430.ctr);
                             defer_ok = (uu___157_2430.defer_ok);
                             smt_ok = (uu___157_2430.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___157_2430.wl_implicits)
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
         (fun uu___129_2633  ->
            match uu___129_2633 with
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
        (fun uu___130_2667  ->
           match uu___130_2667 with
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
        (fun uu___131_2701  ->
           match uu___131_2701 with
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
                    let uu___158_2816 = x  in
                    let uu____2817 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___158_2816.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___158_2816.FStar_Syntax_Syntax.index);
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
                  (let uu___159_4205 = wl  in
                   {
                     attempting = (uu___159_4205.attempting);
                     wl_deferred = (uu___159_4205.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___159_4205.defer_ok);
                     smt_ok = (uu___159_4205.smt_ok);
                     tcenv = (uu___159_4205.tcenv);
                     wl_implicits = (uu___159_4205.wl_implicits)
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
        (let uu___160_4236 = wl  in
         {
           attempting = (uu___160_4236.attempting);
           wl_deferred = (uu___160_4236.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___160_4236.defer_ok);
           smt_ok = (uu___160_4236.smt_ok);
           tcenv = (uu___160_4236.tcenv);
           wl_implicits = (uu___160_4236.wl_implicits)
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
              (fun uu___132_4665  ->
                 match uu___132_4665 with
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
    fun uu___133_5533  ->
      match uu___133_5533 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5539 = f x  in Prims.strcat "Some " uu____5539
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___134_5544  ->
    match uu___134_5544 with
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
  fun uu___135_5564  ->
    match uu___135_5564 with
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
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
          let uu____5638 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5638 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
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
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5831 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5832 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5845 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5852 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
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
            let uu____6180 = FStar_Syntax_Util.head_and_args t  in
            match uu____6180 with
            | (head1,uu____6198) ->
                let uu____6219 =
                  let uu____6220 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6220.FStar_Syntax_Syntax.n  in
                (match uu____6219 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6226 =
                       let uu____6227 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6227 FStar_Option.isSome
                        in
                     if uu____6226
                     then
                       let uu____6246 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6246
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6250 -> FStar_Pervasives_Native.None)
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
              let uu____6383 =
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
              match uu____6383 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____6428 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____6428 with
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
                 uu____6460),uu____6461)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6479 =
                     let uu____6488 = maybe_inline t11  in
                     let uu____6491 = maybe_inline t21  in
                     (uu____6488, uu____6491)  in
                   match uu____6479 with
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
                (uu____6528,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____6529))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6547 =
                     let uu____6556 = maybe_inline t11  in
                     let uu____6559 = maybe_inline t21  in
                     (uu____6556, uu____6559)  in
                   match uu____6547 with
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
            | MisMatch uu____6608 -> fail1 r
            | uu____6617 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6630 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6630
           then
             let uu____6631 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6632 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6633 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____6640 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____6658 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____6658
                    (fun uu____6692  ->
                       match uu____6692 with
                       | (t11,t21) ->
                           let uu____6699 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____6700 =
                             let uu____6701 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____6701  in
                           Prims.strcat uu____6699 uu____6700))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____6631
               uu____6632 uu____6633 uu____6640
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6713 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6713 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___136_6726  ->
    match uu___136_6726 with
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
      let uu___161_6763 = p  in
      let uu____6766 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____6767 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___161_6763.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____6766;
        FStar_TypeChecker_Common.relation =
          (uu___161_6763.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____6767;
        FStar_TypeChecker_Common.element =
          (uu___161_6763.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___161_6763.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___161_6763.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___161_6763.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___161_6763.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___161_6763.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____6781 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____6781
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____6786 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____6808 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____6808 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____6816 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____6816 with
           | (lh,lhs_args) ->
               let uu____6857 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____6857 with
                | (rh,rhs_args) ->
                    let uu____6898 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6911,FStar_Syntax_Syntax.Tm_uvar uu____6912)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____6965 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6988,uu____6989)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____6992,FStar_Syntax_Syntax.Tm_uvar uu____6993)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6996,FStar_Syntax_Syntax.Tm_type uu____6997)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___162_7001 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___162_7001.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___162_7001.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___162_7001.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___162_7001.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___162_7001.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___162_7001.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___162_7001.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___162_7001.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___162_7001.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7004,FStar_Syntax_Syntax.Tm_uvar uu____7005)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___162_7009 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___162_7009.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___162_7009.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___162_7009.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___162_7009.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___162_7009.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___162_7009.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___162_7009.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___162_7009.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___162_7009.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7012,FStar_Syntax_Syntax.Tm_uvar uu____7013)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7016,uu____7017)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7020,FStar_Syntax_Syntax.Tm_uvar uu____7021)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7024,uu____7025) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____6898 with
                     | (rank,tp1) ->
                         let uu____7038 =
                           FStar_All.pipe_right
                             (let uu___163_7042 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___163_7042.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___163_7042.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___163_7042.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___163_7042.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___163_7042.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___163_7042.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___163_7042.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___163_7042.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___163_7042.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7038))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7048 =
            FStar_All.pipe_right
              (let uu___164_7052 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___164_7052.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___164_7052.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___164_7052.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___164_7052.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___164_7052.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___164_7052.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___164_7052.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___164_7052.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___164_7052.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7048)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____7113 probs =
      match uu____7113 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____7194 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____7215 = rank wl.tcenv hd1  in
               (match uu____7215 with
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
                      (let uu____7274 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7278 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____7278)
                          in
                       if uu____7274
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
          let uu____7350 = destruct_flex_t t  in
          match uu____7350 with
          | (uu____7351,u,uu____7353) ->
              FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
                (FStar_Util.for_some
                   (fun uu____7367  ->
                      match uu____7367 with
                      | (y,uu____7373) ->
                          FStar_All.pipe_right bs
                            (FStar_Util.for_some
                               (fun uu____7387  ->
                                  match uu____7387 with
                                  | (x,uu____7393) ->
                                      FStar_Syntax_Syntax.bv_eq x y))))
           in
        let uu____7394 = rank tcenv p  in
        match uu____7394 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____7401 -> true
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
    match projectee with | UDeferred _0 -> true | uu____7428 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____7442 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____7456 -> false
  
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
                        let uu____7508 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____7508 with
                        | (k,uu____7514) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____7524 -> false)))
            | uu____7525 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____7577 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____7583 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____7583 = (Prims.parse_int "0")))
                           in
                        if uu____7577 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____7599 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____7605 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____7605 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____7599)
               in
            let uu____7606 = filter1 u12  in
            let uu____7609 = filter1 u22  in (uu____7606, uu____7609)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____7638 = filter_out_common_univs us1 us2  in
                (match uu____7638 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____7697 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____7697 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____7700 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____7710 =
                          let uu____7711 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____7712 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____7711
                            uu____7712
                           in
                        UFailed uu____7710))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7736 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7736 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7762 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7762 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____7765 ->
                let uu____7770 =
                  let uu____7771 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____7772 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____7771
                    uu____7772 msg
                   in
                UFailed uu____7770
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____7773,uu____7774) ->
              let uu____7775 =
                let uu____7776 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7777 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7776 uu____7777
                 in
              failwith uu____7775
          | (FStar_Syntax_Syntax.U_unknown ,uu____7778) ->
              let uu____7779 =
                let uu____7780 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7781 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7780 uu____7781
                 in
              failwith uu____7779
          | (uu____7782,FStar_Syntax_Syntax.U_bvar uu____7783) ->
              let uu____7784 =
                let uu____7785 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7786 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7785 uu____7786
                 in
              failwith uu____7784
          | (uu____7787,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____7788 =
                let uu____7789 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7790 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7789 uu____7790
                 in
              failwith uu____7788
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____7814 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____7814
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____7828 = occurs_univ v1 u3  in
              if uu____7828
              then
                let uu____7829 =
                  let uu____7830 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7831 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7830 uu____7831
                   in
                try_umax_components u11 u21 uu____7829
              else
                (let uu____7833 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7833)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____7845 = occurs_univ v1 u3  in
              if uu____7845
              then
                let uu____7846 =
                  let uu____7847 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7848 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7847 uu____7848
                   in
                try_umax_components u11 u21 uu____7846
              else
                (let uu____7850 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7850)
          | (FStar_Syntax_Syntax.U_max uu____7851,uu____7852) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7858 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7858
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____7860,FStar_Syntax_Syntax.U_max uu____7861) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7867 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7867
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____7869,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____7870,FStar_Syntax_Syntax.U_name
             uu____7871) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____7872) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____7873) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7874,FStar_Syntax_Syntax.U_succ
             uu____7875) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7876,FStar_Syntax_Syntax.U_zero
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
      let uu____7976 = bc1  in
      match uu____7976 with
      | (bs1,mk_cod1) ->
          let uu____8020 = bc2  in
          (match uu____8020 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____8131 = aux xs ys  in
                     (match uu____8131 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____8214 =
                       let uu____8221 = mk_cod1 xs  in ([], uu____8221)  in
                     let uu____8224 =
                       let uu____8231 = mk_cod2 ys  in ([], uu____8231)  in
                     (uu____8214, uu____8224)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____8254 'Auu____8255 'Auu____8256 .
    ('Auu____8254,'Auu____8255,'Auu____8256 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___137_8269  ->
    match uu___137_8269 with
    | (uu____8278,uu____8279,[]) -> true
    | uu____8282 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8313 = f  in
      match uu____8313 with
      | (uu____8320,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8321;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8322;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8325;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8326;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8327;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____8379  ->
                 match uu____8379 with
                 | (y,uu____8385) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____8491 =
                  let uu____8500 =
                    let uu____8503 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____8503  in
                  ((FStar_List.rev pat_binders), uu____8500)  in
                FStar_Pervasives_Native.Some uu____8491
            | (uu____8518,[]) ->
                let uu____8541 =
                  let uu____8550 =
                    let uu____8553 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____8553  in
                  ((FStar_List.rev pat_binders), uu____8550)  in
                FStar_Pervasives_Native.Some uu____8541
            | ((formal,uu____8569)::formals1,(a,uu____8572)::args2) ->
                let uu____8606 =
                  let uu____8607 = FStar_Syntax_Subst.compress a  in
                  uu____8607.FStar_Syntax_Syntax.n  in
                (match uu____8606 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____8621 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____8621
                     then
                       let uu____8632 =
                         let uu____8635 =
                           FStar_Syntax_Syntax.mk_binder formal  in
                         uu____8635 :: pat_binders  in
                       aux uu____8632 formals1 t_res args2
                     else
                       (let x1 =
                          let uu___165_8638 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___165_8638.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___165_8638.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____8642 =
                            let uu____8643 =
                              let uu____8650 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____8650)  in
                            FStar_Syntax_Syntax.NT uu____8643  in
                          [uu____8642]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        let uu____8657 =
                          let uu____8660 =
                            FStar_Syntax_Syntax.mk_binder
                              (let uu___166_8663 = x1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_8663.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_8663.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort =
                                   (formal.FStar_Syntax_Syntax.sort)
                               })
                             in
                          uu____8660 :: pat_binders  in
                        aux uu____8657 formals2 t_res1 args2)
                 | uu____8664 ->
                     let uu____8665 =
                       let uu____8668 = FStar_Syntax_Syntax.mk_binder formal
                          in
                       uu____8668 :: pat_binders  in
                     aux uu____8665 formals1 t_res args2)
            | ([],args2) ->
                let uu____8692 =
                  let uu____8705 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____8705  in
                (match uu____8692 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____8756 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____8783 ->
               let uu____8784 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____8784 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9056 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9056
       then
         let uu____9057 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9057
       else ());
      (let uu____9059 = next_prob probs  in
       match uu____9059 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___167_9086 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___167_9086.wl_deferred);
               ctr = (uu___167_9086.ctr);
               defer_ok = (uu___167_9086.defer_ok);
               smt_ok = (uu___167_9086.smt_ok);
               tcenv = (uu___167_9086.tcenv);
               wl_implicits = (uu___167_9086.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____9093 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____9093
                then
                  let uu____9094 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____9094
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
                          (let uu___168_9099 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___168_9099.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___168_9099.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___168_9099.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___168_9099.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___168_9099.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___168_9099.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___168_9099.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___168_9099.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___168_9099.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9121 ->
                let uu____9130 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9189  ->
                          match uu____9189 with
                          | (c,uu____9197,uu____9198) -> c < probs.ctr))
                   in
                (match uu____9130 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9239 =
                            let uu____9244 =
                              FStar_List.map
                                (fun uu____9259  ->
                                   match uu____9259 with
                                   | (uu____9270,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9244, (probs.wl_implicits))  in
                          Success uu____9239
                      | uu____9273 ->
                          let uu____9282 =
                            let uu___169_9283 = probs  in
                            let uu____9284 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9303  ->
                                      match uu____9303 with
                                      | (uu____9310,uu____9311,y) -> y))
                               in
                            {
                              attempting = uu____9284;
                              wl_deferred = rest;
                              ctr = (uu___169_9283.ctr);
                              defer_ok = (uu___169_9283.defer_ok);
                              smt_ok = (uu___169_9283.smt_ok);
                              tcenv = (uu___169_9283.tcenv);
                              wl_implicits = (uu___169_9283.wl_implicits)
                            }  in
                          solve env uu____9282))))

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
            let uu____9318 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9318 with
            | USolved wl1 ->
                let uu____9320 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9320
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
                  let uu____9372 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____9372 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9375 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9387;
                  FStar_Syntax_Syntax.vars = uu____9388;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9391;
                  FStar_Syntax_Syntax.vars = uu____9392;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9404,uu____9405) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9412,FStar_Syntax_Syntax.Tm_uinst uu____9413) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9420 -> USolved wl

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
            ((let uu____9430 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____9430
              then
                let uu____9431 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9431 msg
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
              let uu____9516 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____9516 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____9568 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____9568
               then
                 let uu____9569 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____9570 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____9569
                   uu____9570
               else ());
              (let uu____9572 = head_matches_delta env1 () t1 t2  in
               match uu____9572 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____9617 ->
                        let uu____9626 = eq_prob t1 t2 wl2  in
                        (match uu____9626 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____9673 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9688 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____9689 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____9688, uu____9689)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9694 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____9695 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____9694, uu____9695)
                           in
                        (match uu____9673 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____9726 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____9726 with
                               | (t1_hd,t1_args) ->
                                   let uu____9765 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____9765 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____9819 =
                                             let uu____9826 =
                                               let uu____9835 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____9835 :: t1_args  in
                                             let uu____9848 =
                                               let uu____9855 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____9855 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____9896  ->
                                                  fun uu____9897  ->
                                                    fun uu____9898  ->
                                                      match (uu____9896,
                                                              uu____9897,
                                                              uu____9898)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____9940),
                                                         (a2,uu____9942)) ->
                                                          let uu____9967 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____9967
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____9826
                                               uu____9848
                                              in
                                           match uu____9819 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___170_9993 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___170_9993.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___170_9993.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10011 =
                                                 solve env1 wl'  in
                                               (match uu____10011 with
                                                | Success (uu____10014,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___171_10018 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___171_10018.attempting);
                                                           wl_deferred =
                                                             (uu___171_10018.wl_deferred);
                                                           ctr =
                                                             (uu___171_10018.ctr);
                                                           defer_ok =
                                                             (uu___171_10018.defer_ok);
                                                           smt_ok =
                                                             (uu___171_10018.smt_ok);
                                                           tcenv =
                                                             (uu___171_10018.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____10029 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____10061 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____10061 with
                               | (t1_base,p1_opt) ->
                                   let uu____10102 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____10102 with
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
                                              let uu____10233 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____10233
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
                                              let uu____10263 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10263
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
                                              let uu____10293 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10293
                                          | uu____10296 -> t_base  in
                                        let uu____10313 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____10313 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____10327 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____10327, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____10334 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____10334 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____10375 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____10375 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____10416 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____10416
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
                             let uu____10440 = combine t11 t21 wl2  in
                             (match uu____10440 with
                              | (t12,ps,wl3) ->
                                  ((let uu____10473 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "RelCheck")
                                       in
                                    if uu____10473
                                    then
                                      let uu____10474 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____10474
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____10513 ts1 =
              match uu____10513 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____10576 = pairwise out t wl2  in
                       (match uu____10576 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____10612 =
              let uu____10623 = FStar_List.hd ts  in (uu____10623, [], wl1)
               in
            let uu____10632 = FStar_List.tl ts  in
            aux uu____10612 uu____10632  in
          let uu____10639 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____10639 with
          | (this_flex,this_rigid) ->
              let uu____10651 =
                let uu____10652 = FStar_Syntax_Subst.compress this_rigid  in
                uu____10652.FStar_Syntax_Syntax.n  in
              (match uu____10651 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____10673 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____10673
                   then
                     let flex = destruct_flex_t this_flex  in
                     let uu____10675 = quasi_pattern env flex  in
                     (match uu____10675 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env
                            "flex-arrow subtyping, not a quasi pattern"
                            (FStar_TypeChecker_Common.TProb tp)
                      | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                          ((let uu____10693 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____10693
                            then
                              let uu____10694 =
                                FStar_Util.string_of_int
                                  tp.FStar_TypeChecker_Common.pid
                                 in
                              FStar_Util.print1
                                "Trying to solve by imitating arrow:%s\n"
                                uu____10694
                            else ());
                           imitate_arrow (FStar_TypeChecker_Common.TProb tp)
                             env wl flex flex_bs flex_t
                             tp.FStar_TypeChecker_Common.relation this_rigid))
                   else
                     solve env
                       (attempt
                          [FStar_TypeChecker_Common.TProb
                             ((let uu___172_10699 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___172_10699.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___172_10699.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___172_10699.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___172_10699.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___172_10699.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___172_10699.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___172_10699.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___172_10699.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___172_10699.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____10700 ->
                   ((let uu____10702 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____10702
                     then
                       let uu____10703 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____10703
                     else ());
                    (let uu____10705 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____10705 with
                     | (u,_args) ->
                         let uu____10742 =
                           let uu____10743 = FStar_Syntax_Subst.compress u
                              in
                           uu____10743.FStar_Syntax_Syntax.n  in
                         (match uu____10742 with
                          | FStar_Syntax_Syntax.Tm_uvar ctx_uvar ->
                              let equiv1 t =
                                let uu____10753 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____10753 with
                                | (u',uu____10769) ->
                                    let uu____10790 =
                                      let uu____10791 = whnf env u'  in
                                      uu____10791.FStar_Syntax_Syntax.n  in
                                    (match uu____10790 with
                                     | FStar_Syntax_Syntax.Tm_uvar ctx_uvar'
                                         ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____10795 -> false)
                                 in
                              let uu____10796 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___138_10819  ->
                                        match uu___138_10819 with
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
                                             | uu____10828 -> false)
                                        | uu____10831 -> false))
                                 in
                              (match uu____10796 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____10845 = whnf env this_rigid
                                        in
                                     let uu____10846 =
                                       FStar_List.collect
                                         (fun uu___139_10852  ->
                                            match uu___139_10852 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____10858 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____10858]
                                            | uu____10860 -> []) bounds_probs
                                        in
                                     uu____10845 :: uu____10846  in
                                   let uu____10861 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____10861 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____10892 =
                                          let uu____10901 =
                                            destruct_flex_t this_flex  in
                                          match uu____10901 with
                                          | (uu____10910,flex_u,uu____10912)
                                              ->
                                              let bound1 =
                                                let uu____10916 =
                                                  let uu____10917 =
                                                    FStar_Syntax_Subst.compress
                                                      bound
                                                     in
                                                  uu____10917.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____10916 with
                                                | FStar_Syntax_Syntax.Tm_refine
                                                    (x,phi) when
                                                    (tp.FStar_TypeChecker_Common.relation
                                                       =
                                                       FStar_TypeChecker_Common.SUB)
                                                      &&
                                                      (let uu____10929 =
                                                         occurs flex_u
                                                           x.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_Pervasives_Native.snd
                                                         uu____10929)
                                                    ->
                                                    x.FStar_Syntax_Syntax.sort
                                                | uu____10938 -> bound  in
                                              new_problem wl1 env bound1
                                                FStar_TypeChecker_Common.EQ
                                                this_flex
                                                FStar_Pervasives_Native.None
                                                tp.FStar_TypeChecker_Common.loc
                                                (if flip
                                                 then "joining refinements"
                                                 else "meeting refinements")
                                           in
                                        (match uu____10892 with
                                         | (eq_prob,wl2) ->
                                             ((let uu____10953 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "RelCheck")
                                                  in
                                               if uu____10953
                                               then
                                                 let wl' =
                                                   let uu___173_10955 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___173_10955.wl_deferred);
                                                     ctr =
                                                       (uu___173_10955.ctr);
                                                     defer_ok =
                                                       (uu___173_10955.defer_ok);
                                                     smt_ok =
                                                       (uu___173_10955.smt_ok);
                                                     tcenv =
                                                       (uu___173_10955.tcenv);
                                                     wl_implicits =
                                                       (uu___173_10955.wl_implicits)
                                                   }  in
                                                 let uu____10956 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____10956
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10959 =
                                                 solve_t env eq_prob
                                                   (let uu___174_10961 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___174_10961.wl_deferred);
                                                      ctr =
                                                        (uu___174_10961.ctr);
                                                      defer_ok =
                                                        (uu___174_10961.defer_ok);
                                                      smt_ok =
                                                        (uu___174_10961.smt_ok);
                                                      tcenv =
                                                        (uu___174_10961.tcenv);
                                                      wl_implicits =
                                                        (uu___174_10961.wl_implicits)
                                                    })
                                                  in
                                               match uu____10959 with
                                               | Success uu____10962 ->
                                                   let wl3 =
                                                     let uu___175_10968 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___175_10968.wl_deferred);
                                                       ctr =
                                                         (uu___175_10968.ctr);
                                                       defer_ok =
                                                         (uu___175_10968.defer_ok);
                                                       smt_ok =
                                                         (uu___175_10968.smt_ok);
                                                       tcenv =
                                                         (uu___175_10968.tcenv);
                                                       wl_implicits =
                                                         (uu___175_10968.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____10972 =
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
                          | uu____10983 when flip ->
                              let uu____10984 =
                                let uu____10985 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a flex-rigid: %s"
                                  uu____10985
                                 in
                              failwith uu____10984
                          | uu____10986 ->
                              let uu____10987 =
                                let uu____10988 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a rigid-flex: %s"
                                  uu____10988
                                 in
                              failwith uu____10987))))

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
                      (fun uu____11016  ->
                         match uu____11016 with
                         | (x,i) ->
                             let uu____11027 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____11027, i)) bs_lhs
                     in
                  let uu____11028 = lhs  in
                  match uu____11028 with
                  | (uu____11029,u_lhs,uu____11031) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____11144 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____11154 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____11154, univ)
                             in
                          match uu____11144 with
                          | (k,univ) ->
                              let uu____11167 =
                                let uu____11174 =
                                  let uu____11177 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____11177
                                   in
                                copy_uvar u_lhs uu____11174 wl2  in
                              (match uu____11167 with
                               | (uu____11190,u,wl3) ->
                                   let uu____11193 =
                                     let uu____11196 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____11196
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____11193, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____11232 =
                              let uu____11245 =
                                let uu____11254 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____11254 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____11300  ->
                                   fun uu____11301  ->
                                     match (uu____11300, uu____11301) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____11392 =
                                           let uu____11399 =
                                             let uu____11402 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____11402
                                              in
                                           copy_uvar u_lhs uu____11399 wl2
                                            in
                                         (match uu____11392 with
                                          | (uu____11425,t_a,wl3) ->
                                              let uu____11428 =
                                                let uu____11435 =
                                                  let uu____11438 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____11438
                                                   in
                                                copy_uvar u_lhs uu____11435
                                                  wl3
                                                 in
                                              (match uu____11428 with
                                               | (uu____11453,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____11245
                                ([], wl1)
                               in
                            (match uu____11232 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___176_11514 = ct  in
                                   let uu____11515 =
                                     let uu____11518 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____11518
                                      in
                                   let uu____11533 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___176_11514.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___176_11514.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____11515;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____11533;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___176_11514.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___177_11551 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___177_11551.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___177_11551.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____11554 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____11554 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____11608 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____11608 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____11625 =
                                          let uu____11630 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____11630)  in
                                        TERM uu____11625  in
                                      let uu____11631 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____11631 with
                                       | (sub_prob,wl3) ->
                                           let uu____11642 =
                                             let uu____11643 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____11643
                                              in
                                           solve env uu____11642))
                             | (x,imp)::formals2 ->
                                 let uu____11657 =
                                   let uu____11664 =
                                     let uu____11667 =
                                       let uu____11670 =
                                         let uu____11671 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____11671
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____11670
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____11667
                                      in
                                   copy_uvar u_lhs uu____11664 wl1  in
                                 (match uu____11657 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____11695 =
                                          let uu____11698 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____11698
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____11695 t_y
                                         in
                                      let uu____11699 =
                                        let uu____11702 =
                                          let uu____11705 =
                                            let uu____11706 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____11706, imp)  in
                                          [uu____11705]  in
                                        FStar_List.append bs_terms
                                          uu____11702
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____11699 formals2 wl2)
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
              (let uu____11748 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____11748
               then
                 let uu____11749 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____11750 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____11749 (rel_to_string (p_rel orig)) uu____11750
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____11855 = rhs wl1 scope env1 subst1  in
                     (match uu____11855 with
                      | (rhs_prob,wl2) ->
                          ((let uu____11875 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____11875
                            then
                              let uu____11876 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____11876
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___178_11930 = hd1  in
                       let uu____11931 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___178_11930.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___178_11930.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11931
                       }  in
                     let hd21 =
                       let uu___179_11935 = hd2  in
                       let uu____11936 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___179_11935.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___179_11935.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11936
                       }  in
                     let uu____11939 =
                       let uu____11944 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____11944
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____11939 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____11963 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____11963
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____11967 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____11967 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____12022 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____12022
                                  in
                               ((let uu____12034 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____12034
                                 then
                                   let uu____12035 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____12036 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____12035
                                     uu____12036
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____12063 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____12092 = aux wl [] env [] bs1 bs2  in
               match uu____12092 with
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
        (let uu____12143 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____12143 wl)

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
              let uu____12157 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____12157 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____12187 = lhs1  in
              match uu____12187 with
              | (uu____12190,ctx_u,uu____12192) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____12198 ->
                        let uu____12199 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____12199 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____12246 = quasi_pattern env1 lhs1  in
              match uu____12246 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____12276) ->
                  let uu____12281 = lhs1  in
                  (match uu____12281 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____12295 = occurs_check ctx_u rhs1  in
                       (match uu____12295 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____12337 =
                                let uu____12344 =
                                  let uu____12345 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____12345
                                   in
                                FStar_Util.Inl uu____12344  in
                              (uu____12337, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____12365 =
                                 let uu____12366 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____12366  in
                               if uu____12365
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____12386 =
                                    let uu____12393 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____12393  in
                                  let uu____12398 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____12386, uu____12398)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____12460  ->
                     match uu____12460 with
                     | (x,i) ->
                         let uu____12471 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____12471, i)) bs_lhs
                 in
              let uu____12472 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____12472 with
              | (rhs_hd,args) ->
                  let uu____12509 = FStar_Util.prefix args  in
                  (match uu____12509 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____12567 = lhs1  in
                       (match uu____12567 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____12571 =
                              let uu____12582 =
                                let uu____12589 =
                                  let uu____12592 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____12592
                                   in
                                copy_uvar u_lhs uu____12589 wl1  in
                              match uu____12582 with
                              | (uu____12613,t_last_arg,wl2) ->
                                  let uu____12616 =
                                    let uu____12623 =
                                      let uu____12626 =
                                        let uu____12633 =
                                          let uu____12640 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____12640]  in
                                        FStar_List.append bs_lhs uu____12633
                                         in
                                      let uu____12657 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____12626
                                        uu____12657
                                       in
                                    copy_uvar u_lhs uu____12623 wl2  in
                                  (match uu____12616 with
                                   | (uu____12670,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____12676 =
                                         let uu____12683 =
                                           let uu____12686 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____12686
                                            in
                                         copy_uvar u_lhs uu____12683 wl3  in
                                       (match uu____12676 with
                                        | (uu____12699,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____12571 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____12723 =
                                     let uu____12724 =
                                       let uu____12729 =
                                         let uu____12730 =
                                           let uu____12733 =
                                             let uu____12738 =
                                               let uu____12739 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____12739]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____12738
                                              in
                                           uu____12733
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____12730
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____12729)  in
                                     TERM uu____12724  in
                                   [uu____12723]  in
                                 let uu____12760 =
                                   let uu____12767 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____12767 with
                                   | (p1,wl3) ->
                                       let uu____12784 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____12784 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____12760 with
                                  | (sub_probs,wl3) ->
                                      let uu____12811 =
                                        let uu____12812 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____12812  in
                                      solve env1 uu____12811))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____12845 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____12845 with
                | (uu____12860,args) ->
                    (match args with | [] -> false | uu____12888 -> true)
                 in
              let is_arrow rhs2 =
                let uu____12903 =
                  let uu____12904 = FStar_Syntax_Subst.compress rhs2  in
                  uu____12904.FStar_Syntax_Syntax.n  in
                match uu____12903 with
                | FStar_Syntax_Syntax.Tm_arrow uu____12907 -> true
                | uu____12920 -> false  in
              let uu____12921 = quasi_pattern env1 lhs1  in
              match uu____12921 with
              | FStar_Pervasives_Native.None  ->
                  let uu____12932 =
                    let uu____12933 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____12933
                     in
                  giveup_or_defer env1 orig1 wl1 uu____12932
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____12940 = is_app rhs1  in
                  if uu____12940
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____12942 = is_arrow rhs1  in
                     if uu____12942
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____12944 =
                          let uu____12945 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____12945
                           in
                        giveup_or_defer env1 orig1 wl1 uu____12944))
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
                let uu____12948 = lhs  in
                (match uu____12948 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____12952 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____12952 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____12967 =
                              let uu____12970 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____12970
                               in
                            FStar_All.pipe_right uu____12967
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____12985 = occurs_check ctx_uv rhs1  in
                          (match uu____12985 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____13007 =
                                   let uu____13008 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____13008
                                    in
                                 giveup_or_defer env orig wl uu____13007
                               else
                                 (let uu____13010 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____13010
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____13015 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____13015
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____13017 =
                                         let uu____13018 =
                                           names_to_string1 fvs2  in
                                         let uu____13019 =
                                           names_to_string1 fvs1  in
                                         let uu____13020 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____13018 uu____13019
                                           uu____13020
                                          in
                                       giveup_or_defer env orig wl
                                         uu____13017)
                                    else first_order orig env wl lhs rhs1))
                      | uu____13026 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____13030 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____13030 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____13053 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____13053
                             | (FStar_Util.Inl msg,uu____13055) ->
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
                  (let uu____13084 =
                     let uu____13101 = quasi_pattern env lhs  in
                     let uu____13108 = quasi_pattern env rhs  in
                     (uu____13101, uu____13108)  in
                   match uu____13084 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____13151 = lhs  in
                       (match uu____13151 with
                        | ({ FStar_Syntax_Syntax.n = uu____13152;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____13154;_},u_lhs,uu____13156)
                            ->
                            let uu____13159 = rhs  in
                            (match uu____13159 with
                             | (uu____13160,u_rhs,uu____13162) ->
                                 let uu____13163 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____13163
                                 then
                                   let uu____13164 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____13164
                                 else
                                   (let uu____13166 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____13166 with
                                    | (sub_prob,wl1) ->
                                        let uu____13177 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____13177 with
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
                                             let uu____13205 =
                                               let uu____13212 =
                                                 let uu____13215 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____13215
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi: lhs="
                                                    (Prims.strcat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.strcat ", rhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))
                                                 wl1 range gamma_w ctx_w
                                                 uu____13212
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____13205 with
                                              | (uu____13218,w,wl2) ->
                                                  let w_app =
                                                    let uu____13224 =
                                                      let uu____13229 =
                                                        FStar_List.map
                                                          (fun uu____13238 
                                                             ->
                                                             match uu____13238
                                                             with
                                                             | (z,uu____13244)
                                                                 ->
                                                                 let uu____13245
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____13245)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____13229
                                                       in
                                                    uu____13224
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____13249 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "RelCheck")
                                                       in
                                                    if uu____13249
                                                    then
                                                      let uu____13250 =
                                                        flex_t_to_string lhs
                                                         in
                                                      let uu____13251 =
                                                        flex_t_to_string rhs
                                                         in
                                                      let uu____13252 =
                                                        let uu____13253 =
                                                          destruct_flex_t w
                                                           in
                                                        flex_t_to_string
                                                          uu____13253
                                                         in
                                                      FStar_Util.print3
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s"
                                                        uu____13250
                                                        uu____13251
                                                        uu____13252
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____13265 =
                                                          let uu____13270 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____13270)
                                                           in
                                                        TERM uu____13265  in
                                                      let uu____13271 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____13271
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____13276 =
                                                             let uu____13281
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
                                                               uu____13281)
                                                              in
                                                           TERM uu____13276
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____13282 =
                                                      let uu____13283 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____13283
                                                       in
                                                    solve env uu____13282)))))))
                   | uu____13284 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____13352 = head_matches_delta env1 wl1 t1 t2  in
           match uu____13352 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____13383,uu____13384) ->
                    let rec may_relate head3 =
                      let uu____13411 =
                        let uu____13412 = FStar_Syntax_Subst.compress head3
                           in
                        uu____13412.FStar_Syntax_Syntax.n  in
                      match uu____13411 with
                      | FStar_Syntax_Syntax.Tm_name uu____13415 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____13416 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13439;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____13440;
                            FStar_Syntax_Syntax.fv_qual = uu____13441;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13444;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____13445;
                            FStar_Syntax_Syntax.fv_qual = uu____13446;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____13450,uu____13451) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____13493) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____13499) ->
                          may_relate t
                      | uu____13504 -> false  in
                    let uu____13505 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____13505
                    then
                      let uu____13506 =
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
                                 let uu____13538 =
                                   let uu____13539 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____13539 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____13538
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____13544 = has_type_guard t1 t2  in
                             (uu____13544, wl1)
                           else
                             (let uu____13550 = has_type_guard t2 t1  in
                              (uu____13550, wl1)))
                         in
                      (match uu____13506 with
                       | (guard,wl2) ->
                           let uu____13557 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____13557)
                    else
                      (let uu____13559 =
                         let uu____13560 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13561 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____13560 uu____13561
                          in
                       giveup env1 uu____13559 orig)
                | (uu____13562,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___180_13576 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___180_13576.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___180_13576.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___180_13576.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___180_13576.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___180_13576.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___180_13576.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___180_13576.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___180_13576.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____13577,FStar_Pervasives_Native.None ) ->
                    ((let uu____13589 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13589
                      then
                        let uu____13590 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____13591 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____13592 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____13593 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____13590 uu____13591 uu____13592 uu____13593
                      else ());
                     (let uu____13595 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____13595 with
                      | (head11,args1) ->
                          let uu____13632 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____13632 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____13686 =
                                   let uu____13687 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____13688 = args_to_string args1  in
                                   let uu____13689 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____13690 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____13687 uu____13688 uu____13689
                                     uu____13690
                                    in
                                 giveup env1 uu____13686 orig
                               else
                                 (let uu____13692 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____13699 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____13699 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____13692
                                  then
                                    let uu____13700 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____13700 with
                                    | USolved wl2 ->
                                        let uu____13702 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____13702
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____13706 =
                                       base_and_refinement env1 t1  in
                                     match uu____13706 with
                                     | (base1,refinement1) ->
                                         let uu____13731 =
                                           base_and_refinement env1 t2  in
                                         (match uu____13731 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____13788 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____13788 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____13792 =
                                                          FStar_List.fold_right2
                                                            (fun uu____13825 
                                                               ->
                                                               fun
                                                                 uu____13826 
                                                                 ->
                                                                 fun
                                                                   uu____13827
                                                                    ->
                                                                   match 
                                                                    (uu____13825,
                                                                    uu____13826,
                                                                    uu____13827)
                                                                   with
                                                                   | 
                                                                   ((a,uu____13863),
                                                                    (a',uu____13865),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____13886
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____13886
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
                                                        (match uu____13792
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____13914
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____13914
                                                               then
                                                                 let uu____13915
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____13915
                                                               else ());
                                                              (let formula =
                                                                 let uu____13920
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____13920
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
                                               | uu____13928 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___181_13968 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___181_13968.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____13971 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____13971
          then
            let uu____13972 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____13972
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____13977 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "RelCheck")
                 in
              if uu____13977
              then
                let uu____13978 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____13979 =
                  let uu____13980 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____13981 =
                    let uu____13982 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____13982  in
                  Prims.strcat uu____13980 uu____13981  in
                let uu____13983 =
                  let uu____13984 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____13985 =
                    let uu____13986 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____13986  in
                  Prims.strcat uu____13984 uu____13985  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____13978
                  uu____13979 uu____13983
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____13989,uu____13990) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____14015,FStar_Syntax_Syntax.Tm_delayed uu____14016) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____14041,uu____14042) ->
                  let uu____14069 =
                    let uu___182_14070 = problem  in
                    let uu____14071 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___182_14070.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____14071;
                      FStar_TypeChecker_Common.relation =
                        (uu___182_14070.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___182_14070.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___182_14070.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___182_14070.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___182_14070.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___182_14070.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___182_14070.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___182_14070.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14069 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____14072,uu____14073) ->
                  let uu____14080 =
                    let uu___183_14081 = problem  in
                    let uu____14082 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___183_14081.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____14082;
                      FStar_TypeChecker_Common.relation =
                        (uu___183_14081.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___183_14081.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___183_14081.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___183_14081.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___183_14081.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___183_14081.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___183_14081.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___183_14081.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14080 wl
              | (uu____14083,FStar_Syntax_Syntax.Tm_ascribed uu____14084) ->
                  let uu____14111 =
                    let uu___184_14112 = problem  in
                    let uu____14113 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___184_14112.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___184_14112.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___184_14112.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____14113;
                      FStar_TypeChecker_Common.element =
                        (uu___184_14112.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___184_14112.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___184_14112.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___184_14112.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___184_14112.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___184_14112.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14111 wl
              | (uu____14114,FStar_Syntax_Syntax.Tm_meta uu____14115) ->
                  let uu____14122 =
                    let uu___185_14123 = problem  in
                    let uu____14124 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___185_14123.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___185_14123.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___185_14123.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____14124;
                      FStar_TypeChecker_Common.element =
                        (uu___185_14123.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___185_14123.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___185_14123.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___185_14123.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___185_14123.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___185_14123.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14122 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____14126),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____14128)) ->
                  let uu____14137 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____14137
              | (FStar_Syntax_Syntax.Tm_bvar uu____14138,uu____14139) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____14140,FStar_Syntax_Syntax.Tm_bvar uu____14141) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___140_14200 =
                    match uu___140_14200 with
                    | [] -> c
                    | bs ->
                        let uu____14222 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____14222
                     in
                  let uu____14231 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____14231 with
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
                                    let uu____14354 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____14354
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
                  let mk_t t l uu___141_14429 =
                    match uu___141_14429 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____14463 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____14463 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____14582 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____14583 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____14582
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____14583 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____14584,uu____14585) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____14612 -> true
                    | uu____14629 -> false  in
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
                      (let uu____14670 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___186_14678 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___186_14678.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___186_14678.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___186_14678.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___186_14678.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___186_14678.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___186_14678.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___186_14678.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___186_14678.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___186_14678.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___186_14678.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___186_14678.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___186_14678.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___186_14678.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___186_14678.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___186_14678.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___186_14678.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___186_14678.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___186_14678.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___186_14678.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___186_14678.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___186_14678.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___186_14678.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___186_14678.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___186_14678.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___186_14678.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___186_14678.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___186_14678.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___186_14678.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___186_14678.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___186_14678.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___186_14678.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___186_14678.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___186_14678.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___186_14678.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___186_14678.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____14670 with
                       | (uu____14681,ty,uu____14683) ->
                           let uu____14684 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____14684)
                     in
                  let uu____14685 =
                    let uu____14698 = maybe_eta t1  in
                    let uu____14703 = maybe_eta t2  in
                    (uu____14698, uu____14703)  in
                  (match uu____14685 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___187_14727 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___187_14727.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___187_14727.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___187_14727.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___187_14727.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___187_14727.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___187_14727.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___187_14727.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___187_14727.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____14738 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14738
                       then
                         let uu____14739 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14739 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_14748 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_14748.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_14748.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_14748.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_14748.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_14748.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_14748.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_14748.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_14748.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____14760 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14760
                       then
                         let uu____14761 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14761 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_14770 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_14770.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_14770.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_14770.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_14770.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_14770.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_14770.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_14770.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_14770.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____14772 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____14785,FStar_Syntax_Syntax.Tm_abs uu____14786) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____14813 -> true
                    | uu____14830 -> false  in
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
                      (let uu____14871 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___186_14879 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___186_14879.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___186_14879.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___186_14879.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___186_14879.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___186_14879.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___186_14879.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___186_14879.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___186_14879.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___186_14879.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___186_14879.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___186_14879.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___186_14879.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___186_14879.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___186_14879.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___186_14879.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___186_14879.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___186_14879.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___186_14879.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___186_14879.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___186_14879.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___186_14879.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___186_14879.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___186_14879.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___186_14879.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___186_14879.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___186_14879.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___186_14879.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___186_14879.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___186_14879.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___186_14879.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___186_14879.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___186_14879.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___186_14879.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___186_14879.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___186_14879.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____14871 with
                       | (uu____14882,ty,uu____14884) ->
                           let uu____14885 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____14885)
                     in
                  let uu____14886 =
                    let uu____14899 = maybe_eta t1  in
                    let uu____14904 = maybe_eta t2  in
                    (uu____14899, uu____14904)  in
                  (match uu____14886 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___187_14928 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___187_14928.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___187_14928.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___187_14928.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___187_14928.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___187_14928.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___187_14928.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___187_14928.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___187_14928.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____14939 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14939
                       then
                         let uu____14940 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14940 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_14949 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_14949.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_14949.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_14949.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_14949.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_14949.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_14949.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_14949.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_14949.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____14961 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14961
                       then
                         let uu____14962 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14962 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_14971 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_14971.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_14971.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_14971.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_14971.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_14971.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_14971.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_14971.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_14971.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____14973 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____15001 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____15001) &&
                       (let uu____15005 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____15005))
                      &&
                      (let uu____15012 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____15012 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___142_15024 =
                             match uu___142_15024 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____15025 -> true
                             | uu____15026 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____15027 -> false)
                     in
                  let uu____15028 = as_refinement should_delta env wl t1  in
                  (match uu____15028 with
                   | (x11,phi1) ->
                       let uu____15035 = as_refinement should_delta env wl t2
                          in
                       (match uu____15035 with
                        | (x21,phi21) ->
                            let uu____15042 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____15042 with
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
                                   let uu____15108 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____15108
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____15120 =
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
                                   let uu____15131 =
                                     let uu____15136 =
                                       let uu____15143 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____15143]  in
                                     mk_t_problem wl1 uu____15136 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____15131 with
                                    | (ref_prob,wl2) ->
                                        let uu____15158 =
                                          solve env1
                                            (let uu___189_15160 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___189_15160.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___189_15160.smt_ok);
                                               tcenv = (uu___189_15160.tcenv);
                                               wl_implicits =
                                                 (uu___189_15160.wl_implicits)
                                             })
                                           in
                                        (match uu____15158 with
                                         | Failed uu____15167 -> fallback ()
                                         | Success uu____15172 ->
                                             let guard =
                                               let uu____15180 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____15180
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___190_15189 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___190_15189.attempting);
                                                 wl_deferred =
                                                   (uu___190_15189.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___190_15189.defer_ok);
                                                 smt_ok =
                                                   (uu___190_15189.smt_ok);
                                                 tcenv =
                                                   (uu___190_15189.tcenv);
                                                 wl_implicits =
                                                   (uu___190_15189.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15191,FStar_Syntax_Syntax.Tm_uvar uu____15192) ->
                  let uu____15193 = destruct_flex_t t1  in
                  let uu____15194 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15193 uu____15194
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15195;
                    FStar_Syntax_Syntax.pos = uu____15196;
                    FStar_Syntax_Syntax.vars = uu____15197;_},uu____15198),FStar_Syntax_Syntax.Tm_uvar
                 uu____15199) ->
                  let uu____15220 = destruct_flex_t t1  in
                  let uu____15221 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15220 uu____15221
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15222,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15223;
                    FStar_Syntax_Syntax.pos = uu____15224;
                    FStar_Syntax_Syntax.vars = uu____15225;_},uu____15226))
                  ->
                  let uu____15247 = destruct_flex_t t1  in
                  let uu____15248 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15247 uu____15248
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15249;
                    FStar_Syntax_Syntax.pos = uu____15250;
                    FStar_Syntax_Syntax.vars = uu____15251;_},uu____15252),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15253;
                    FStar_Syntax_Syntax.pos = uu____15254;
                    FStar_Syntax_Syntax.vars = uu____15255;_},uu____15256))
                  ->
                  let uu____15297 = destruct_flex_t t1  in
                  let uu____15298 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15297 uu____15298
              | (FStar_Syntax_Syntax.Tm_uvar uu____15299,uu____15300) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____15301 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____15301 t2
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15302;
                    FStar_Syntax_Syntax.pos = uu____15303;
                    FStar_Syntax_Syntax.vars = uu____15304;_},uu____15305),uu____15306)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____15327 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____15327 t2
              | (uu____15328,FStar_Syntax_Syntax.Tm_uvar uu____15329) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____15330,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15331;
                    FStar_Syntax_Syntax.pos = uu____15332;
                    FStar_Syntax_Syntax.vars = uu____15333;_},uu____15334))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15355,FStar_Syntax_Syntax.Tm_arrow uu____15356) ->
                  solve_t' env
                    (let uu___191_15370 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___191_15370.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___191_15370.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___191_15370.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___191_15370.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___191_15370.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___191_15370.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___191_15370.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___191_15370.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___191_15370.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15371;
                    FStar_Syntax_Syntax.pos = uu____15372;
                    FStar_Syntax_Syntax.vars = uu____15373;_},uu____15374),FStar_Syntax_Syntax.Tm_arrow
                 uu____15375) ->
                  solve_t' env
                    (let uu___191_15409 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___191_15409.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___191_15409.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___191_15409.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___191_15409.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___191_15409.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___191_15409.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___191_15409.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___191_15409.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___191_15409.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____15410,FStar_Syntax_Syntax.Tm_uvar uu____15411) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____15412,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15413;
                    FStar_Syntax_Syntax.pos = uu____15414;
                    FStar_Syntax_Syntax.vars = uu____15415;_},uu____15416))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____15437,uu____15438) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15439;
                    FStar_Syntax_Syntax.pos = uu____15440;
                    FStar_Syntax_Syntax.vars = uu____15441;_},uu____15442),uu____15443)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____15464,uu____15465) ->
                  let t21 =
                    let uu____15473 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____15473  in
                  solve_t env
                    (let uu___192_15499 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___192_15499.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___192_15499.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___192_15499.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___192_15499.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___192_15499.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___192_15499.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___192_15499.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___192_15499.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___192_15499.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____15500,FStar_Syntax_Syntax.Tm_refine uu____15501) ->
                  let t11 =
                    let uu____15509 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____15509  in
                  solve_t env
                    (let uu___193_15535 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___193_15535.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___193_15535.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___193_15535.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___193_15535.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___193_15535.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___193_15535.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___193_15535.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___193_15535.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___193_15535.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____15612 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____15612 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____15833 = br1  in
                             (match uu____15833 with
                              | (p1,w1,uu____15858) ->
                                  let uu____15875 = br2  in
                                  (match uu____15875 with
                                   | (p2,w2,uu____15894) ->
                                       let uu____15899 =
                                         let uu____15900 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____15900  in
                                       if uu____15899
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____15916 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____15916 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____15949 = br2  in
                                              (match uu____15949 with
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
                                                     let uu____15984 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____15984
                                                      in
                                                   let uu____15995 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____16018,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____16035) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____16078 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____16078
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____15995
                                                     (fun uu____16120  ->
                                                        match uu____16120
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____16141 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____16141
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____16156
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____16156
                                                                   (fun
                                                                    uu____16180
                                                                     ->
                                                                    match uu____16180
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
                         | uu____16265 -> FStar_Pervasives_Native.None  in
                       let uu____16302 = solve_branches wl1 brs1 brs2  in
                       (match uu____16302 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____16333,uu____16334) ->
                  let head1 =
                    let uu____16358 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16358
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16398 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16398
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16438 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16438
                    then
                      let uu____16439 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16440 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16441 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16439 uu____16440 uu____16441
                    else ());
                   (let uu____16443 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16443
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16450 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16450
                       then
                         let uu____16451 =
                           let uu____16458 =
                             let uu____16459 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16459 = FStar_Syntax_Util.Equal  in
                           if uu____16458
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16469 = mk_eq2 wl orig t1 t2  in
                              match uu____16469 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16451 with
                         | (guard,wl1) ->
                             let uu____16490 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16490
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____16493,uu____16494) ->
                  let head1 =
                    let uu____16502 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16502
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16542 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16542
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16582 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16582
                    then
                      let uu____16583 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16584 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16585 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16583 uu____16584 uu____16585
                    else ());
                   (let uu____16587 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16587
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16594 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16594
                       then
                         let uu____16595 =
                           let uu____16602 =
                             let uu____16603 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16603 = FStar_Syntax_Util.Equal  in
                           if uu____16602
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16613 = mk_eq2 wl orig t1 t2  in
                              match uu____16613 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16595 with
                         | (guard,wl1) ->
                             let uu____16634 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16634
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____16637,uu____16638) ->
                  let head1 =
                    let uu____16640 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16640
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16680 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16680
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16720 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16720
                    then
                      let uu____16721 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16722 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16723 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16721 uu____16722 uu____16723
                    else ());
                   (let uu____16725 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16725
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16732 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16732
                       then
                         let uu____16733 =
                           let uu____16740 =
                             let uu____16741 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16741 = FStar_Syntax_Util.Equal  in
                           if uu____16740
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16751 = mk_eq2 wl orig t1 t2  in
                              match uu____16751 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16733 with
                         | (guard,wl1) ->
                             let uu____16772 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16772
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____16775,uu____16776) ->
                  let head1 =
                    let uu____16778 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16778
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16818 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16818
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16858 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16858
                    then
                      let uu____16859 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16860 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16861 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16859 uu____16860 uu____16861
                    else ());
                   (let uu____16863 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16863
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16870 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16870
                       then
                         let uu____16871 =
                           let uu____16878 =
                             let uu____16879 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16879 = FStar_Syntax_Util.Equal  in
                           if uu____16878
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16889 = mk_eq2 wl orig t1 t2  in
                              match uu____16889 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16871 with
                         | (guard,wl1) ->
                             let uu____16910 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16910
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____16913,uu____16914) ->
                  let head1 =
                    let uu____16916 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16916
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16956 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16956
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16996 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16996
                    then
                      let uu____16997 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16998 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16999 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16997 uu____16998 uu____16999
                    else ());
                   (let uu____17001 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17001
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17008 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17008
                       then
                         let uu____17009 =
                           let uu____17016 =
                             let uu____17017 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17017 = FStar_Syntax_Util.Equal  in
                           if uu____17016
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17027 = mk_eq2 wl orig t1 t2  in
                              match uu____17027 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17009 with
                         | (guard,wl1) ->
                             let uu____17048 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17048
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____17051,uu____17052) ->
                  let head1 =
                    let uu____17068 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17068
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17108 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17108
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17148 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17148
                    then
                      let uu____17149 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17150 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17151 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17149 uu____17150 uu____17151
                    else ());
                   (let uu____17153 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17153
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17160 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17160
                       then
                         let uu____17161 =
                           let uu____17168 =
                             let uu____17169 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17169 = FStar_Syntax_Util.Equal  in
                           if uu____17168
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17179 = mk_eq2 wl orig t1 t2  in
                              match uu____17179 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17161 with
                         | (guard,wl1) ->
                             let uu____17200 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17200
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17203,FStar_Syntax_Syntax.Tm_match uu____17204) ->
                  let head1 =
                    let uu____17228 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17228
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17268 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17268
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17308 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17308
                    then
                      let uu____17309 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17310 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17311 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17309 uu____17310 uu____17311
                    else ());
                   (let uu____17313 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17313
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17320 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17320
                       then
                         let uu____17321 =
                           let uu____17328 =
                             let uu____17329 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17329 = FStar_Syntax_Util.Equal  in
                           if uu____17328
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17339 = mk_eq2 wl orig t1 t2  in
                              match uu____17339 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17321 with
                         | (guard,wl1) ->
                             let uu____17360 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17360
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17363,FStar_Syntax_Syntax.Tm_uinst uu____17364) ->
                  let head1 =
                    let uu____17372 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17372
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17412 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17412
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17452 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17452
                    then
                      let uu____17453 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17454 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17455 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17453 uu____17454 uu____17455
                    else ());
                   (let uu____17457 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17457
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17464 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17464
                       then
                         let uu____17465 =
                           let uu____17472 =
                             let uu____17473 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17473 = FStar_Syntax_Util.Equal  in
                           if uu____17472
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17483 = mk_eq2 wl orig t1 t2  in
                              match uu____17483 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17465 with
                         | (guard,wl1) ->
                             let uu____17504 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17504
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17507,FStar_Syntax_Syntax.Tm_name uu____17508) ->
                  let head1 =
                    let uu____17510 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17510
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17550 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17550
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17590 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17590
                    then
                      let uu____17591 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17592 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17593 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17591 uu____17592 uu____17593
                    else ());
                   (let uu____17595 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17595
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17602 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17602
                       then
                         let uu____17603 =
                           let uu____17610 =
                             let uu____17611 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17611 = FStar_Syntax_Util.Equal  in
                           if uu____17610
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17621 = mk_eq2 wl orig t1 t2  in
                              match uu____17621 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17603 with
                         | (guard,wl1) ->
                             let uu____17642 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17642
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17645,FStar_Syntax_Syntax.Tm_constant uu____17646) ->
                  let head1 =
                    let uu____17648 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17648
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17688 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17688
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17728 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17728
                    then
                      let uu____17729 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17730 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17731 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17729 uu____17730 uu____17731
                    else ());
                   (let uu____17733 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17733
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17740 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17740
                       then
                         let uu____17741 =
                           let uu____17748 =
                             let uu____17749 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17749 = FStar_Syntax_Util.Equal  in
                           if uu____17748
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17759 = mk_eq2 wl orig t1 t2  in
                              match uu____17759 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17741 with
                         | (guard,wl1) ->
                             let uu____17780 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17780
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17783,FStar_Syntax_Syntax.Tm_fvar uu____17784) ->
                  let head1 =
                    let uu____17786 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17786
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17826 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17826
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17866 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17866
                    then
                      let uu____17867 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17868 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17869 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17867 uu____17868 uu____17869
                    else ());
                   (let uu____17871 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17871
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17878 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17878
                       then
                         let uu____17879 =
                           let uu____17886 =
                             let uu____17887 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17887 = FStar_Syntax_Util.Equal  in
                           if uu____17886
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17897 = mk_eq2 wl orig t1 t2  in
                              match uu____17897 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17879 with
                         | (guard,wl1) ->
                             let uu____17918 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17918
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17921,FStar_Syntax_Syntax.Tm_app uu____17922) ->
                  let head1 =
                    let uu____17938 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17938
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17978 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17978
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18018 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____18018
                    then
                      let uu____18019 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18020 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18021 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18019 uu____18020 uu____18021
                    else ());
                   (let uu____18023 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18023
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18030 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18030
                       then
                         let uu____18031 =
                           let uu____18038 =
                             let uu____18039 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18039 = FStar_Syntax_Util.Equal  in
                           if uu____18038
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18049 = mk_eq2 wl orig t1 t2  in
                              match uu____18049 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18031 with
                         | (guard,wl1) ->
                             let uu____18070 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18070
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____18073,FStar_Syntax_Syntax.Tm_let uu____18074) ->
                  let uu____18099 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____18099
                  then
                    let uu____18100 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____18100
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____18102,uu____18103) ->
                  let uu____18116 =
                    let uu____18121 =
                      let uu____18122 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____18123 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____18124 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____18125 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____18122 uu____18123 uu____18124 uu____18125
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____18121)
                     in
                  FStar_Errors.raise_error uu____18116
                    t1.FStar_Syntax_Syntax.pos
              | (uu____18126,FStar_Syntax_Syntax.Tm_let uu____18127) ->
                  let uu____18140 =
                    let uu____18145 =
                      let uu____18146 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____18147 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____18148 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____18149 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____18146 uu____18147 uu____18148 uu____18149
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____18145)
                     in
                  FStar_Errors.raise_error uu____18140
                    t1.FStar_Syntax_Syntax.pos
              | uu____18150 -> giveup env "head tag mismatch" orig))))

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
          (let uu____18209 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____18209
           then
             let uu____18210 =
               let uu____18211 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____18211  in
             let uu____18212 =
               let uu____18213 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____18213  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____18210 uu____18212
           else ());
          (let uu____18215 =
             let uu____18216 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____18216  in
           if uu____18215
           then
             let uu____18217 =
               let uu____18218 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____18219 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____18218 uu____18219
                in
             giveup env uu____18217 orig
           else
             (let uu____18221 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____18221 with
              | (ret_sub_prob,wl1) ->
                  let uu____18228 =
                    FStar_List.fold_right2
                      (fun uu____18261  ->
                         fun uu____18262  ->
                           fun uu____18263  ->
                             match (uu____18261, uu____18262, uu____18263)
                             with
                             | ((a1,uu____18299),(a2,uu____18301),(arg_sub_probs,wl2))
                                 ->
                                 let uu____18322 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____18322 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____18228 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____18351 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____18351  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____18381 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____18384)::[] -> wp1
              | uu____18401 ->
                  let uu____18410 =
                    let uu____18411 =
                      let uu____18412 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____18412  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____18411
                     in
                  failwith uu____18410
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____18418 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____18418]
              | x -> x  in
            let uu____18420 =
              let uu____18429 =
                let uu____18436 =
                  let uu____18437 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____18437 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____18436  in
              [uu____18429]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____18420;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____18450 = lift_c1 ()  in solve_eq uu____18450 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___143_18456  ->
                       match uu___143_18456 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____18457 -> false))
                in
             let uu____18458 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____18484)::uu____18485,(wp2,uu____18487)::uu____18488)
                   -> (wp1, wp2)
               | uu____18541 ->
                   let uu____18562 =
                     let uu____18567 =
                       let uu____18568 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____18569 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____18568 uu____18569
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____18567)
                      in
                   FStar_Errors.raise_error uu____18562
                     env.FStar_TypeChecker_Env.range
                in
             match uu____18458 with
             | (wpc1,wpc2) ->
                 let uu____18576 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____18576
                 then
                   let uu____18579 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____18579 wl
                 else
                   (let uu____18581 =
                      let uu____18588 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____18588  in
                    match uu____18581 with
                    | (c2_decl,qualifiers) ->
                        let uu____18609 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____18609
                        then
                          let c1_repr =
                            let uu____18613 =
                              let uu____18614 =
                                let uu____18615 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____18615  in
                              let uu____18616 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____18614 uu____18616
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____18613
                             in
                          let c2_repr =
                            let uu____18618 =
                              let uu____18619 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____18620 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____18619 uu____18620
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____18618
                             in
                          let uu____18621 =
                            let uu____18626 =
                              let uu____18627 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____18628 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____18627 uu____18628
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____18626
                             in
                          (match uu____18621 with
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
                                 ((let uu____18642 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____18642
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____18645 =
                                     let uu____18652 =
                                       let uu____18653 =
                                         let uu____18668 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____18671 =
                                           let uu____18680 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____18687 =
                                             let uu____18696 =
                                               let uu____18703 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____18703
                                                in
                                             [uu____18696]  in
                                           uu____18680 :: uu____18687  in
                                         (uu____18668, uu____18671)  in
                                       FStar_Syntax_Syntax.Tm_app uu____18653
                                        in
                                     FStar_Syntax_Syntax.mk uu____18652  in
                                   uu____18645 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____18738 =
                                    let uu____18745 =
                                      let uu____18746 =
                                        let uu____18761 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____18764 =
                                          let uu____18773 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____18780 =
                                            let uu____18789 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____18796 =
                                              let uu____18805 =
                                                let uu____18812 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____18812
                                                 in
                                              [uu____18805]  in
                                            uu____18789 :: uu____18796  in
                                          uu____18773 :: uu____18780  in
                                        (uu____18761, uu____18764)  in
                                      FStar_Syntax_Syntax.Tm_app uu____18746
                                       in
                                    FStar_Syntax_Syntax.mk uu____18745  in
                                  uu____18738 FStar_Pervasives_Native.None r)
                              in
                           let uu____18850 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____18850 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____18858 =
                                   let uu____18861 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____18861
                                    in
                                 solve_prob orig uu____18858 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____18868 = FStar_Util.physical_equality c1 c2  in
        if uu____18868
        then
          let uu____18869 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____18869
        else
          ((let uu____18872 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____18872
            then
              let uu____18873 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____18874 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____18873
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____18874
            else ());
           (let uu____18876 =
              let uu____18885 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____18888 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____18885, uu____18888)  in
            match uu____18876 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18906),FStar_Syntax_Syntax.Total
                    (t2,uu____18908)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____18925 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18925 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____18926,FStar_Syntax_Syntax.Total uu____18927) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18945),FStar_Syntax_Syntax.Total
                    (t2,uu____18947)) ->
                     let uu____18964 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18964 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18966),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18968)) ->
                     let uu____18985 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18985 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18987),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18989)) ->
                     let uu____19006 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____19006 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____19007,FStar_Syntax_Syntax.Comp uu____19008) ->
                     let uu____19017 =
                       let uu___194_19020 = problem  in
                       let uu____19023 =
                         let uu____19024 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19024
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___194_19020.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____19023;
                         FStar_TypeChecker_Common.relation =
                           (uu___194_19020.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___194_19020.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___194_19020.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___194_19020.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___194_19020.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___194_19020.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___194_19020.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___194_19020.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19017 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____19025,FStar_Syntax_Syntax.Comp uu____19026) ->
                     let uu____19035 =
                       let uu___194_19038 = problem  in
                       let uu____19041 =
                         let uu____19042 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19042
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___194_19038.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____19041;
                         FStar_TypeChecker_Common.relation =
                           (uu___194_19038.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___194_19038.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___194_19038.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___194_19038.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___194_19038.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___194_19038.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___194_19038.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___194_19038.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19035 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____19043,FStar_Syntax_Syntax.GTotal uu____19044) ->
                     let uu____19053 =
                       let uu___195_19056 = problem  in
                       let uu____19059 =
                         let uu____19060 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19060
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___195_19056.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___195_19056.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___195_19056.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____19059;
                         FStar_TypeChecker_Common.element =
                           (uu___195_19056.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___195_19056.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___195_19056.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___195_19056.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___195_19056.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___195_19056.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19053 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____19061,FStar_Syntax_Syntax.Total uu____19062) ->
                     let uu____19071 =
                       let uu___195_19074 = problem  in
                       let uu____19077 =
                         let uu____19078 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19078
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___195_19074.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___195_19074.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___195_19074.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____19077;
                         FStar_TypeChecker_Common.element =
                           (uu___195_19074.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___195_19074.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___195_19074.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___195_19074.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___195_19074.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___195_19074.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19071 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____19079,FStar_Syntax_Syntax.Comp uu____19080) ->
                     let uu____19081 =
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
                     if uu____19081
                     then
                       let uu____19082 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____19082 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____19086 =
                            let uu____19091 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____19091
                            then (c1_comp, c2_comp)
                            else
                              (let uu____19097 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____19098 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____19097, uu____19098))
                             in
                          match uu____19086 with
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
                           (let uu____19105 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____19105
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____19107 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____19107 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____19110 =
                                  let uu____19111 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____19112 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____19111 uu____19112
                                   in
                                giveup env uu____19110 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____19119 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____19152  ->
              match uu____19152 with
              | (uu____19163,tm,uu____19165,uu____19166,uu____19167) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____19119 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____19200 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____19200 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____19218 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____19246  ->
                match uu____19246 with
                | (u1,u2) ->
                    let uu____19253 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____19254 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____19253 uu____19254))
         in
      FStar_All.pipe_right uu____19218 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____19281,[])) -> "{}"
      | uu____19306 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____19329 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____19329
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____19332 =
              FStar_List.map
                (fun uu____19342  ->
                   match uu____19342 with
                   | (uu____19347,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____19332 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____19352 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____19352 imps
  
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
                  let uu____19405 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ExplainRel")
                     in
                  if uu____19405
                  then
                    let uu____19406 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____19407 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____19406
                      (rel_to_string rel) uu____19407
                  else "TOP"  in
                let uu____19409 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____19409 with
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
              let uu____19466 =
                let uu____19469 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____19469
                 in
              FStar_Syntax_Syntax.new_bv uu____19466 t1  in
            let uu____19472 =
              let uu____19477 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____19477
               in
            match uu____19472 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____19533 = FStar_Options.eager_inference ()  in
          if uu____19533
          then
            let uu___196_19534 = probs  in
            {
              attempting = (uu___196_19534.attempting);
              wl_deferred = (uu___196_19534.wl_deferred);
              ctr = (uu___196_19534.ctr);
              defer_ok = false;
              smt_ok = (uu___196_19534.smt_ok);
              tcenv = (uu___196_19534.tcenv);
              wl_implicits = (uu___196_19534.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____19554 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____19554
              then
                let uu____19555 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____19555
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
          ((let uu____19577 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____19577
            then
              let uu____19578 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____19578
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____19582 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____19582
             then
               let uu____19583 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____19583
             else ());
            (let f2 =
               let uu____19586 =
                 let uu____19587 = FStar_Syntax_Util.unmeta f1  in
                 uu____19587.FStar_Syntax_Syntax.n  in
               match uu____19586 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____19591 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___197_19592 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___197_19592.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___197_19592.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___197_19592.FStar_TypeChecker_Env.implicits)
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
            let uu____19706 =
              let uu____19707 =
                let uu____19708 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____19708;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____19707  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____19706
  
let with_guard_no_simp :
  'Auu____19723 .
    'Auu____19723 ->
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
            let uu____19746 =
              let uu____19747 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____19747;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____19746
  
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
          (let uu____19787 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____19787
           then
             let uu____19788 = FStar_Syntax_Print.term_to_string t1  in
             let uu____19789 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____19788
               uu____19789
           else ());
          (let uu____19791 =
             let uu____19796 = empty_worklist env  in
             let uu____19797 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____19796 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____19797
              in
           match uu____19791 with
           | (prob,wl) ->
               let g =
                 let uu____19805 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____19825  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____19805  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____19869 = try_teq true env t1 t2  in
        match uu____19869 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____19873 = FStar_TypeChecker_Env.get_range env  in
              let uu____19874 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____19873 uu____19874);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____19881 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____19881
              then
                let uu____19882 = FStar_Syntax_Print.term_to_string t1  in
                let uu____19883 = FStar_Syntax_Print.term_to_string t2  in
                let uu____19884 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____19882
                  uu____19883 uu____19884
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
          let uu____19906 = FStar_TypeChecker_Env.get_range env  in
          let uu____19907 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____19906 uu____19907
  
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
        (let uu____19932 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____19932
         then
           let uu____19933 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____19934 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____19933 uu____19934
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____19937 =
           let uu____19944 = empty_worklist env  in
           let uu____19945 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____19944 env c1 rel c2 FStar_Pervasives_Native.None
             uu____19945 "sub_comp"
            in
         match uu____19937 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____19955 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____19975  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____19955)
  
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
      fun uu____20030  ->
        match uu____20030 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____20073 =
                 let uu____20078 =
                   let uu____20079 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____20080 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____20079 uu____20080
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____20078)  in
               let uu____20081 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____20073 uu____20081)
               in
            let equiv1 v1 v' =
              let uu____20093 =
                let uu____20098 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____20099 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____20098, uu____20099)  in
              match uu____20093 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____20118 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____20148 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____20148 with
                      | FStar_Syntax_Syntax.U_unif uu____20155 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____20184  ->
                                    match uu____20184 with
                                    | (u,v') ->
                                        let uu____20193 = equiv1 v1 v'  in
                                        if uu____20193
                                        then
                                          let uu____20196 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____20196 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____20212 -> []))
               in
            let uu____20217 =
              let wl =
                let uu___198_20221 = empty_worklist env  in
                {
                  attempting = (uu___198_20221.attempting);
                  wl_deferred = (uu___198_20221.wl_deferred);
                  ctr = (uu___198_20221.ctr);
                  defer_ok = false;
                  smt_ok = (uu___198_20221.smt_ok);
                  tcenv = (uu___198_20221.tcenv);
                  wl_implicits = (uu___198_20221.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____20239  ->
                      match uu____20239 with
                      | (lb,v1) ->
                          let uu____20246 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____20246 with
                           | USolved wl1 -> ()
                           | uu____20248 -> fail1 lb v1)))
               in
            let rec check_ineq uu____20258 =
              match uu____20258 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____20267) -> true
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
                      uu____20290,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____20292,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____20303) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____20310,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____20318 -> false)
               in
            let uu____20323 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____20338  ->
                      match uu____20338 with
                      | (u,v1) ->
                          let uu____20345 = check_ineq (u, v1)  in
                          if uu____20345
                          then true
                          else
                            ((let uu____20348 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____20348
                              then
                                let uu____20349 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____20350 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____20349
                                  uu____20350
                              else ());
                             false)))
               in
            if uu____20323
            then ()
            else
              ((let uu____20354 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____20354
                then
                  ((let uu____20356 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____20356);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____20366 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____20366))
                else ());
               (let uu____20376 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____20376))
  
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
        let fail1 uu____20443 =
          match uu____20443 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___199_20464 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___199_20464.attempting);
            wl_deferred = (uu___199_20464.wl_deferred);
            ctr = (uu___199_20464.ctr);
            defer_ok;
            smt_ok = (uu___199_20464.smt_ok);
            tcenv = (uu___199_20464.tcenv);
            wl_implicits = (uu___199_20464.wl_implicits)
          }  in
        (let uu____20466 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____20466
         then
           let uu____20467 = FStar_Util.string_of_bool defer_ok  in
           let uu____20468 = wl_to_string wl  in
           let uu____20469 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____20467 uu____20468 uu____20469
         else ());
        (let g1 =
           let uu____20482 = solve_and_commit env wl fail1  in
           match uu____20482 with
           | FStar_Pervasives_Native.Some
               (uu____20489::uu____20490,uu____20491) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___200_20516 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___200_20516.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___200_20516.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____20527 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___201_20535 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___201_20535.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___201_20535.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___201_20535.FStar_TypeChecker_Env.implicits)
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
    let uu____20583 = FStar_ST.op_Bang last_proof_ns  in
    match uu____20583 with
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
            let uu___202_20706 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___202_20706.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___202_20706.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___202_20706.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____20707 =
            let uu____20708 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____20708  in
          if uu____20707
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____20716 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____20717 =
                       let uu____20718 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____20718
                        in
                     FStar_Errors.diag uu____20716 uu____20717)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____20722 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____20723 =
                        let uu____20724 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____20724
                         in
                      FStar_Errors.diag uu____20722 uu____20723)
                   else ();
                   (let uu____20727 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____20727 "discharge_guard'"
                      env vc1);
                   (let uu____20728 = check_trivial vc1  in
                    match uu____20728 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____20735 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____20736 =
                                let uu____20737 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____20737
                                 in
                              FStar_Errors.diag uu____20735 uu____20736)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____20742 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____20743 =
                                let uu____20744 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____20744
                                 in
                              FStar_Errors.diag uu____20742 uu____20743)
                           else ();
                           (let vcs =
                              let uu____20757 = FStar_Options.use_tactics ()
                                 in
                              if uu____20757
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____20779  ->
                                     (let uu____20781 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____20781);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____20824  ->
                                              match uu____20824 with
                                              | (env1,goal,opts) ->
                                                  let uu____20840 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____20840, opts)))))
                              else
                                (let uu____20842 =
                                   let uu____20849 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____20849)  in
                                 [uu____20842])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____20886  ->
                                    match uu____20886 with
                                    | (env1,goal,opts) ->
                                        let uu____20902 = check_trivial goal
                                           in
                                        (match uu____20902 with
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
                                                (let uu____20910 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____20911 =
                                                   let uu____20912 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____20913 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____20912 uu____20913
                                                    in
                                                 FStar_Errors.diag
                                                   uu____20910 uu____20911)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____20916 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____20917 =
                                                   let uu____20918 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____20918
                                                    in
                                                 FStar_Errors.diag
                                                   uu____20916 uu____20917)
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
      let uu____20932 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____20932 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____20939 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____20939
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____20950 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____20950 with
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
            let uu____20983 = FStar_Syntax_Util.head_and_args u  in
            match uu____20983 with
            | (hd1,uu____20999) ->
                let uu____21020 =
                  let uu____21021 = FStar_Syntax_Subst.compress u  in
                  uu____21021.FStar_Syntax_Syntax.n  in
                (match uu____21020 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____21024 -> true
                 | uu____21025 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____21045 = acc  in
            match uu____21045 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____21107 = hd1  in
                     (match uu____21107 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____21124 = unresolved tm  in
                             if uu____21124
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___203_21137 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___203_21137.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___203_21137.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___203_21137.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___203_21137.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___203_21137.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___203_21137.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___203_21137.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___203_21137.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___203_21137.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___203_21137.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___203_21137.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___203_21137.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___203_21137.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___203_21137.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___203_21137.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___203_21137.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___203_21137.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___203_21137.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___203_21137.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___203_21137.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___203_21137.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___203_21137.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___203_21137.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___203_21137.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___203_21137.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___203_21137.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___203_21137.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___203_21137.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___203_21137.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___203_21137.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___203_21137.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___203_21137.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___203_21137.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___203_21137.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___203_21137.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___203_21137.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___203_21137.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___204_21140 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___204_21140.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___204_21140.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___204_21140.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___204_21140.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___204_21140.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___204_21140.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___204_21140.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___204_21140.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___204_21140.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___204_21140.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___204_21140.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___204_21140.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___204_21140.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___204_21140.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___204_21140.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___204_21140.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___204_21140.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___204_21140.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___204_21140.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___204_21140.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___204_21140.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___204_21140.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___204_21140.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___204_21140.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___204_21140.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___204_21140.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___204_21140.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___204_21140.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___204_21140.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___204_21140.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___204_21140.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___204_21140.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___204_21140.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___204_21140.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___204_21140.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___204_21140.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___204_21140.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____21143 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "RelCheck")
                                    in
                                 if uu____21143
                                 then
                                   let uu____21144 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____21145 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____21146 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____21147 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____21144 uu____21145 uu____21146
                                     reason uu____21147
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e when FStar_Errors.handleable e ->
                                       ((let uu____21158 =
                                           let uu____21167 =
                                             let uu____21174 =
                                               let uu____21175 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____21176 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____21175 uu____21176
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____21174, r)
                                              in
                                           [uu____21167]  in
                                         FStar_Errors.add_errors uu____21158);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___207_21190 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___207_21190.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___207_21190.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___207_21190.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____21193 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____21200  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____21193 with
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
          let uu___208_21212 = g  in
          let uu____21213 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___208_21212.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___208_21212.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___208_21212.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____21213
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
        let uu____21267 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____21267 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____21278 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____21278
      | (reason,e,ctx_u,r,should_check)::uu____21284 ->
          let uu____21307 =
            let uu____21312 =
              let uu____21313 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____21314 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____21315 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____21313 uu____21314 reason uu____21315
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____21312)
             in
          FStar_Errors.raise_error uu____21307 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___209_21326 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___209_21326.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___209_21326.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___209_21326.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____21341 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____21341 with
      | FStar_Pervasives_Native.Some uu____21347 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21363 = try_teq false env t1 t2  in
        match uu____21363 with
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
        (let uu____21397 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21397
         then
           let uu____21398 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____21399 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____21398
             uu____21399
         else ());
        (let uu____21401 =
           let uu____21408 = empty_worklist env  in
           new_t_prob uu____21408 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____21401 with
         | (prob,x,wl) ->
             let g =
               let uu____21421 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____21441  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____21421  in
             ((let uu____21471 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____21471
               then
                 let uu____21472 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____21473 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____21474 =
                   let uu____21475 = FStar_Util.must g  in
                   guard_to_string env uu____21475  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____21472 uu____21473 uu____21474
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
        let uu____21509 = check_subtyping env t1 t2  in
        match uu____21509 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____21528 =
              let uu____21529 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____21529 g  in
            FStar_Pervasives_Native.Some uu____21528
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21547 = check_subtyping env t1 t2  in
        match uu____21547 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____21566 =
              let uu____21567 =
                let uu____21568 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____21568]  in
              close_guard env uu____21567 g  in
            FStar_Pervasives_Native.Some uu____21566
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____21597 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21597
         then
           let uu____21598 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____21599 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____21598
             uu____21599
         else ());
        (let uu____21601 =
           let uu____21608 = empty_worklist env  in
           new_t_prob uu____21608 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____21601 with
         | (prob,x,wl) ->
             let g =
               let uu____21615 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____21635  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____21615  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____21666 =
                      let uu____21667 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____21667]  in
                    close_guard env uu____21666 g1  in
                  discharge_guard_nosmt env g2))
  