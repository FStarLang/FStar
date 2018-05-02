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
                  true gamma binders;
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
                  let uu____1135 =
                    let uu____1138 =
                      term_to_string p.FStar_TypeChecker_Common.logical_guard
                       in
                    let uu____1139 =
                      let uu____1142 =
                        match p.FStar_TypeChecker_Common.element with
                        | FStar_Pervasives_Native.None  -> "none"
                        | FStar_Pervasives_Native.Some t -> term_to_string t
                         in
                      [uu____1142]  in
                    uu____1138 :: uu____1139  in
                  uu____1134 :: uu____1135  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1131
                 in
              uu____1127 :: uu____1128  in
            uu____1123 :: uu____1124  in
          FStar_Util.format
            "\n%s:\t%s \n\t\t%s\n\t%s\n\twith guard %s\n\telement= %s\n"
            uu____1120
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1147 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1148 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1149 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1147 uu____1148
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1149
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___117_1159  ->
      match uu___117_1159 with
      | UNIV (u,t) ->
          let x =
            let uu____1163 = FStar_Options.hide_uvar_nums ()  in
            if uu____1163
            then "?"
            else
              (let uu____1165 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1165 FStar_Util.string_of_int)
             in
          let uu____1166 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1166
      | TERM (u,t) ->
          let x =
            let uu____1170 = FStar_Options.hide_uvar_nums ()  in
            if uu____1170
            then "?"
            else
              (let uu____1172 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1172 FStar_Util.string_of_int)
             in
          let uu____1173 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1173
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1188 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1188 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1202 =
      let uu____1205 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1205
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1202 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1218 .
    (FStar_Syntax_Syntax.term,'Auu____1218) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1236 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1254  ->
              match uu____1254 with
              | (x,uu____1260) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1236 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1268 =
      let uu____1269 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1269  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1268;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___150_1301 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___150_1301.wl_deferred);
          ctr = (uu___150_1301.ctr);
          defer_ok = (uu___150_1301.defer_ok);
          smt_ok;
          tcenv = (uu___150_1301.tcenv);
          wl_implicits = (uu___150_1301.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1308 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1308,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___151_1331 = empty_worklist env  in
      let uu____1332 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1332;
        wl_deferred = (uu___151_1331.wl_deferred);
        ctr = (uu___151_1331.ctr);
        defer_ok = (uu___151_1331.defer_ok);
        smt_ok = (uu___151_1331.smt_ok);
        tcenv = (uu___151_1331.tcenv);
        wl_implicits = (uu___151_1331.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___152_1352 = wl  in
        {
          attempting = (uu___152_1352.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___152_1352.ctr);
          defer_ok = (uu___152_1352.defer_ok);
          smt_ok = (uu___152_1352.smt_ok);
          tcenv = (uu___152_1352.tcenv);
          wl_implicits = (uu___152_1352.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___153_1373 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___153_1373.wl_deferred);
        ctr = (uu___153_1373.ctr);
        defer_ok = (uu___153_1373.defer_ok);
        smt_ok = (uu___153_1373.smt_ok);
        tcenv = (uu___153_1373.tcenv);
        wl_implicits = (uu___153_1373.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1390 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1390
         then
           let uu____1391 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1391
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___118_1397  ->
    match uu___118_1397 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1402 .
    'Auu____1402 FStar_TypeChecker_Common.problem ->
      'Auu____1402 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___154_1414 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___154_1414.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___154_1414.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___154_1414.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___154_1414.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___154_1414.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___154_1414.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___154_1414.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1421 .
    'Auu____1421 FStar_TypeChecker_Common.problem ->
      'Auu____1421 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___119_1438  ->
    match uu___119_1438 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___120_1453  ->
    match uu___120_1453 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___155_1459 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___155_1459.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___155_1459.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___155_1459.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___155_1459.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___155_1459.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___155_1459.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___155_1459.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___155_1459.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___155_1459.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___156_1467 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___156_1467.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___156_1467.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___156_1467.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___156_1467.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___156_1467.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___156_1467.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___156_1467.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___156_1467.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___156_1467.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___121_1479  ->
      match uu___121_1479 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___122_1484  ->
    match uu___122_1484 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___123_1495  ->
    match uu___123_1495 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___124_1508  ->
    match uu___124_1508 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___125_1521  ->
    match uu___125_1521 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___126_1532  ->
    match uu___126_1532 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___127_1547  ->
    match uu___127_1547 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1566 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1566) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1594 =
          let uu____1595 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1595  in
        if uu____1594
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1629)::bs ->
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
        let uu____1696 =
          let uu____1697 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1697  in
        if uu____1696
        then ()
        else
          (let uu____1699 =
             let uu____1702 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1702
              in
           def_check_closed_in (p_loc prob) msg uu____1699 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1732 =
         let uu____1733 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1733  in
       if uu____1732
       then ()
       else
         (let uu____1735 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1735));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1747 -> ())
  
let mk_eq2 :
  'Auu____1759 .
    worklist ->
      'Auu____1759 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1788 = FStar_Syntax_Util.type_u ()  in
          match uu____1788 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1800 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type false
                 in
              (match uu____1800 with
               | (uu____1811,tt,wl1) ->
                   let uu____1814 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1814, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___128_1819  ->
    match uu___128_1819 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1835 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1835 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1847  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1945 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1945 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1945 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1945 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2011 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2011  in
                  let uu____2014 =
                    let uu____2021 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2021
                      guard_ty false
                     in
                  match uu____2014 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2042 ->
                            let uu____2049 =
                              let uu____2054 =
                                FStar_List.map
                                  (fun uu____2067  ->
                                     match uu____2067 with
                                     | (x,i) ->
                                         let uu____2078 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2078, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2054  in
                            uu____2049 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2081 =
                        let uu____2084 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2084;
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
                      (uu____2081, wl1)
  
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
                  let uu____2147 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2147 with
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
                  let uu____2224 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2224 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2259 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2259 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2259 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2259 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2310 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2365 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2365]  in
                        let uu____2378 =
                          let uu____2381 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2381  in
                        let uu____2384 =
                          let uu____2387 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2387  in
                        (bs, uu____2378, uu____2384)
                     in
                  match uu____2310 with
                  | (bs,lg_ty,elt) ->
                      let uu____2427 =
                        let uu____2434 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___157_2442 = wl  in
                           {
                             attempting = (uu___157_2442.attempting);
                             wl_deferred = (uu___157_2442.wl_deferred);
                             ctr = (uu___157_2442.ctr);
                             defer_ok = (uu___157_2442.defer_ok);
                             smt_ok = (uu___157_2442.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___157_2442.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2434
                          lg_ty false
                         in
                      (match uu____2427 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2454 =
                                   let uu____2459 =
                                     let uu____2460 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2460]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2459
                                    in
                                 uu____2454 FStar_Pervasives_Native.None loc
                              in
                           let uu____2481 =
                             let uu____2484 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2484;
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
                           (uu____2481, wl1))
  
let problem_using_guard :
  'Auu____2501 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2501 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2501 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2501 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2538 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2538;
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
  'Auu____2549 .
    worklist ->
      'Auu____2549 FStar_TypeChecker_Common.problem ->
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
        let uu____2599 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____2599
        then
          let uu____2600 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2601 = prob_to_string env d  in
          let uu____2602 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2600 uu____2601 uu____2602 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2608 -> failwith "impossible"  in
           let uu____2609 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2621 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2622 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2621, uu____2622)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2626 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2627 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2626, uu____2627)
              in
           match uu____2609 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___129_2645  ->
            match uu___129_2645 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2657 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___130_2679  ->
           match uu___130_2679 with
           | UNIV uu____2682 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2689 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2689
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
        (fun uu___131_2713  ->
           match uu___131_2713 with
           | UNIV (u',t) ->
               let uu____2718 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2718
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2722 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2733 =
        let uu____2734 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2734
         in
      FStar_Syntax_Subst.compress uu____2733
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2745 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2745
  
let norm_arg :
  'Auu____2752 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2752) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2752)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2775 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2775, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2816  ->
              match uu____2816 with
              | (x,imp) ->
                  let uu____2827 =
                    let uu___158_2828 = x  in
                    let uu____2829 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___158_2828.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___158_2828.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2829
                    }  in
                  (uu____2827, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2850 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2850
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2854 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2854
        | uu____2857 -> u2  in
      let uu____2858 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2858
  
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
                (let uu____2972 = norm_refinement env t12  in
                 match uu____2972 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2987;
                     FStar_Syntax_Syntax.vars = uu____2988;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3014 =
                       let uu____3015 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3016 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3015 uu____3016
                        in
                     failwith uu____3014)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3030 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3030
          | FStar_Syntax_Syntax.Tm_uinst uu____3031 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3066 =
                   let uu____3067 = FStar_Syntax_Subst.compress t1'  in
                   uu____3067.FStar_Syntax_Syntax.n  in
                 match uu____3066 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3082 -> aux true t1'
                 | uu____3089 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3104 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3133 =
                   let uu____3134 = FStar_Syntax_Subst.compress t1'  in
                   uu____3134.FStar_Syntax_Syntax.n  in
                 match uu____3133 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3149 -> aux true t1'
                 | uu____3156 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3171 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3214 =
                   let uu____3215 = FStar_Syntax_Subst.compress t1'  in
                   uu____3215.FStar_Syntax_Syntax.n  in
                 match uu____3214 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3230 -> aux true t1'
                 | uu____3237 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3252 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3267 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3282 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3297 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3312 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3339 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3370 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3391 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3406 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3433 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3470 ->
              let uu____3477 =
                let uu____3478 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3479 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3478 uu____3479
                 in
              failwith uu____3477
          | FStar_Syntax_Syntax.Tm_ascribed uu____3492 ->
              let uu____3519 =
                let uu____3520 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3521 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3520 uu____3521
                 in
              failwith uu____3519
          | FStar_Syntax_Syntax.Tm_delayed uu____3534 ->
              let uu____3559 =
                let uu____3560 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3561 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3560 uu____3561
                 in
              failwith uu____3559
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3574 =
                let uu____3575 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3576 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3575 uu____3576
                 in
              failwith uu____3574
           in
        let uu____3589 = whnf env t1  in aux false uu____3589
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3620 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3620 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3651 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3651 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3687 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3687, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3698 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3698 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3723 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3723 with
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
  fun uu____3800  ->
    match uu____3800 with
    | (t_base,refopt) ->
        let uu____3833 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3833 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3873 =
      let uu____3876 =
        let uu____3879 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3902  ->
                  match uu____3902 with | (uu____3909,uu____3910,x) -> x))
           in
        FStar_List.append wl.attempting uu____3879  in
      FStar_List.map (wl_prob_to_string wl) uu____3876  in
    FStar_All.pipe_right uu____3873 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____3924 .
    ('Auu____3924,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3935  ->
    match uu____3935 with
    | (uu____3942,c,args) ->
        let uu____3945 = print_ctx_uvar c  in
        let uu____3946 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3945 uu____3946
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3952 =
      let uu____3953 = FStar_Syntax_Subst.compress t  in
      uu____3953.FStar_Syntax_Syntax.n  in
    match uu____3952 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3956 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3957;
           FStar_Syntax_Syntax.pos = uu____3958;
           FStar_Syntax_Syntax.vars = uu____3959;_},uu____3960)
        -> true
    | uu____3981 -> false
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> flex_t) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar uv -> (t, uv, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uv;
           FStar_Syntax_Syntax.pos = uu____3999;
           FStar_Syntax_Syntax.vars = uu____4000;_},args)
        -> (t, uv, args)
    | uu____4022 -> failwith "Not a flex-uvar"
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4038 =
          let uu____4051 =
            let uu____4052 = FStar_Syntax_Subst.compress k  in
            uu____4052.FStar_Syntax_Syntax.n  in
          match uu____4051 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4105 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4105)
              else
                (let uu____4119 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4119 with
                 | (ys',t1,uu____4142) ->
                     let uu____4147 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4147))
          | uu____4188 ->
              let uu____4189 =
                let uu____4200 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4200)  in
              ((ys, t), uu____4189)
           in
        match uu____4038 with
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
                 let uu____4249 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4249 c  in
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
               (let uu____4323 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4323
                then
                  let uu____4324 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4325 = print_ctx_uvar uv  in
                  let uu____4326 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4324 uu____4325 uu____4326
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
             let uu____4332 = p_guard_uvar prob  in
             match uu____4332 with
             | (xs,uv) ->
                 let fail1 uu____4344 =
                   let uu____4345 =
                     let uu____4346 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4347 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4346 uu____4347
                      in
                   failwith uu____4345  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____4397  ->
                           match uu____4397 with
                           | (a,i) ->
                               let uu____4410 =
                                 let uu____4411 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____4411.FStar_Syntax_Syntax.n  in
                               (match uu____4410 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____4429 -> (fail1 (); []))))
                    in
                 ((let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____4437 =
                     let uu____4438 = is_flex g  in
                     Prims.op_Negation uu____4438  in
                   if uu____4437
                   then (if resolve_ok then () else fail1 ())
                   else
                     (let uu____4441 = destruct_flex_t g  in
                      match uu____4441 with
                      | (uu____4442,uv1,args) ->
                          let uu____4445 = args_as_binders args  in
                          assign_solution uu____4445 uv1 phi));
                  commit uvis;
                  (let uu___159_4447 = wl  in
                   {
                     attempting = (uu___159_4447.attempting);
                     wl_deferred = (uu___159_4447.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___159_4447.defer_ok);
                     smt_ok = (uu___159_4447.smt_ok);
                     tcenv = (uu___159_4447.tcenv);
                     wl_implicits = (uu___159_4447.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4468 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____4468
         then
           let uu____4469 = FStar_Util.string_of_int pid  in
           let uu____4470 =
             let uu____4471 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4471 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4469 uu____4470
         else ());
        commit sol;
        (let uu___160_4478 = wl  in
         {
           attempting = (uu___160_4478.attempting);
           wl_deferred = (uu___160_4478.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___160_4478.defer_ok);
           smt_ok = (uu___160_4478.smt_ok);
           tcenv = (uu___160_4478.tcenv);
           wl_implicits = (uu___160_4478.wl_implicits)
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
             | (uu____4540,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4566 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4566
              in
           (let uu____4572 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____4572
            then
              let uu____4573 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4574 =
                let uu____4575 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4575 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4573 uu____4574
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
        let uu____4600 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4600 FStar_Util.set_elements  in
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
      let uu____4634 = occurs uk t  in
      match uu____4634 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4663 =
                 let uu____4664 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4665 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4664 uu____4665
                  in
               FStar_Pervasives_Native.Some uu____4663)
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
            let uu____4754 = maximal_prefix bs_tail bs'_tail  in
            (match uu____4754 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____4798 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____4846  ->
             match uu____4846 with
             | (x,uu____4856) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____4869 = FStar_List.last bs  in
      match uu____4869 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____4887) ->
          let uu____4892 =
            FStar_Util.prefix_until
              (fun uu___132_4907  ->
                 match uu___132_4907 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____4909 -> false) g
             in
          (match uu____4892 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____4922,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____4958 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____4958 with
        | (pfx,uu____4968) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____4980 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____4980 with
             | (uu____4987,src',wl1) ->
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
      let uu____5067 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____5121  ->
                fun uu____5122  ->
                  match (uu____5121, uu____5122) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____5203 =
                        let uu____5204 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____5204  in
                      if uu____5203
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____5229 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____5229
                         then
                           let uu____5242 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____5242)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____5067 with | (isect,uu____5279) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5308 'Auu____5309 .
    (FStar_Syntax_Syntax.bv,'Auu____5308) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5309) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5366  ->
              fun uu____5367  ->
                match (uu____5366, uu____5367) with
                | ((a,uu____5385),(b,uu____5387)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5402 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5402) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5432  ->
           match uu____5432 with
           | (y,uu____5438) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5449 'Auu____5450 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5449) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5450)
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
                   let uu____5559 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5559
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____5567 =
                        let uu____5570 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____5570 :: seen  in
                      aux uu____5567 args2)
               | uu____5571 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____5601 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5638 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5644 -> false
  
let string_of_option :
  'Auu____5651 .
    ('Auu____5651 -> Prims.string) ->
      'Auu____5651 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___133_5666  ->
      match uu___133_5666 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5672 = f x  in Prims.strcat "Some " uu____5672
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___134_5677  ->
    match uu___134_5677 with
    | MisMatch (d1,d2) ->
        let uu____5688 =
          let uu____5689 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5690 =
            let uu____5691 =
              let uu____5692 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5692 ")"  in
            Prims.strcat ") (" uu____5691  in
          Prims.strcat uu____5689 uu____5690  in
        Prims.strcat "MisMatch (" uu____5688
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___135_5697  ->
    match uu___135_5697 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5712 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5742 = m2 ()  in
          (match uu____5742 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5757 -> HeadMatch)
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
          let uu____5771 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5771 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____5782 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5805 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5814 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5842 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5842
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5843 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5844 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5845 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5846 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5859 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5883) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5889,uu____5890) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5932) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5953;
             FStar_Syntax_Syntax.index = uu____5954;
             FStar_Syntax_Syntax.sort = t2;_},uu____5956)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5963 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5964 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5965 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5978 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5985 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6003 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6003
  
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
            let uu____6030 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6030
            then FullMatch
            else
              (let uu____6032 =
                 let uu____6041 =
                   let uu____6044 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6044  in
                 let uu____6045 =
                   let uu____6048 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6048  in
                 (uu____6041, uu____6045)  in
               MisMatch uu____6032)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6054),FStar_Syntax_Syntax.Tm_uinst (g,uu____6056)) ->
            let uu____6065 = head_matches env f g  in
            FStar_All.pipe_right uu____6065 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6068 = FStar_Const.eq_const c d  in
            if uu____6068
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar uv,FStar_Syntax_Syntax.Tm_uvar uv') ->
            let uu____6076 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6076
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6083),FStar_Syntax_Syntax.Tm_refine (y,uu____6085)) ->
            let uu____6094 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6094 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6096),uu____6097) ->
            let uu____6102 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6102 head_match
        | (uu____6103,FStar_Syntax_Syntax.Tm_refine (x,uu____6105)) ->
            let uu____6110 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6110 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6111,FStar_Syntax_Syntax.Tm_type
           uu____6112) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6113,FStar_Syntax_Syntax.Tm_arrow uu____6114) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6140),FStar_Syntax_Syntax.Tm_app (head',uu____6142))
            ->
            let uu____6183 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6183 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6185),uu____6186) ->
            let uu____6207 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6207 head_match
        | (uu____6208,FStar_Syntax_Syntax.Tm_app (head1,uu____6210)) ->
            let uu____6231 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6231 head_match
        | uu____6232 ->
            let uu____6237 =
              let uu____6246 = delta_depth_of_term env t11  in
              let uu____6249 = delta_depth_of_term env t21  in
              (uu____6246, uu____6249)  in
            MisMatch uu____6237
  
let head_matches_delta :
  'Auu____6266 .
    FStar_TypeChecker_Env.env ->
      'Auu____6266 ->
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
            let uu____6313 = FStar_Syntax_Util.head_and_args t  in
            match uu____6313 with
            | (head1,uu____6331) ->
                let uu____6352 =
                  let uu____6353 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6353.FStar_Syntax_Syntax.n  in
                (match uu____6352 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6359 =
                       let uu____6360 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6360 FStar_Option.isSome
                        in
                     if uu____6359
                     then
                       let uu____6379 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6379
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6383 -> FStar_Pervasives_Native.None)
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
              let uu____6516 =
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
              match uu____6516 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____6561 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____6561 with
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
                 uu____6593),uu____6594)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6612 =
                     let uu____6621 = maybe_inline t11  in
                     let uu____6624 = maybe_inline t21  in
                     (uu____6621, uu____6624)  in
                   match uu____6612 with
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
                (uu____6661,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____6662))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6680 =
                     let uu____6689 = maybe_inline t11  in
                     let uu____6692 = maybe_inline t21  in
                     (uu____6689, uu____6692)  in
                   match uu____6680 with
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
            | MisMatch uu____6741 -> fail1 r
            | uu____6750 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6763 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6763
           then
             let uu____6764 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6765 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6766 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____6773 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____6791 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____6791
                    (fun uu____6825  ->
                       match uu____6825 with
                       | (t11,t21) ->
                           let uu____6832 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____6833 =
                             let uu____6834 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____6834  in
                           Prims.strcat uu____6832 uu____6833))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____6764
               uu____6765 uu____6766 uu____6773
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6846 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6846 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___136_6859  ->
    match uu___136_6859 with
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
      let uu___161_6896 = p  in
      let uu____6899 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____6900 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___161_6896.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____6899;
        FStar_TypeChecker_Common.relation =
          (uu___161_6896.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____6900;
        FStar_TypeChecker_Common.element =
          (uu___161_6896.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___161_6896.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___161_6896.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___161_6896.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___161_6896.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___161_6896.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____6914 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____6914
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____6919 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____6941 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____6941 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____6949 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____6949 with
           | (lh,lhs_args) ->
               let uu____6990 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____6990 with
                | (rh,rhs_args) ->
                    let uu____7031 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7044,FStar_Syntax_Syntax.Tm_uvar uu____7045)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7098 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7121,uu____7122)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7125,FStar_Syntax_Syntax.Tm_uvar uu____7126)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7129,FStar_Syntax_Syntax.Tm_arrow uu____7130)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___162_7146 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___162_7146.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___162_7146.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___162_7146.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___162_7146.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___162_7146.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___162_7146.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___162_7146.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___162_7146.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___162_7146.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7149,FStar_Syntax_Syntax.Tm_type uu____7150)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___162_7154 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___162_7154.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___162_7154.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___162_7154.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___162_7154.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___162_7154.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___162_7154.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___162_7154.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___162_7154.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___162_7154.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7157,FStar_Syntax_Syntax.Tm_uvar uu____7158)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___162_7162 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___162_7162.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___162_7162.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___162_7162.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___162_7162.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___162_7162.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___162_7162.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___162_7162.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___162_7162.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___162_7162.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7165,FStar_Syntax_Syntax.Tm_uvar uu____7166)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7169,uu____7170)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7173,FStar_Syntax_Syntax.Tm_uvar uu____7174)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7177,uu____7178) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7031 with
                     | (rank,tp1) ->
                         let uu____7191 =
                           FStar_All.pipe_right
                             (let uu___163_7195 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___163_7195.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___163_7195.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___163_7195.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___163_7195.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___163_7195.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___163_7195.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___163_7195.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___163_7195.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___163_7195.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7191))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7201 =
            FStar_All.pipe_right
              (let uu___164_7205 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___164_7205.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___164_7205.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___164_7205.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___164_7205.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___164_7205.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___164_7205.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___164_7205.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___164_7205.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___164_7205.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7201)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____7266 probs =
      match uu____7266 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____7347 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____7368 = rank wl.tcenv hd1  in
               (match uu____7368 with
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
                      (let uu____7427 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7431 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____7431)
                          in
                       if uu____7427
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
          let uu____7503 = destruct_flex_t t  in
          match uu____7503 with
          | (uu____7504,u,uu____7506) ->
              FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
                (FStar_Util.for_some
                   (fun uu____7520  ->
                      match uu____7520 with
                      | (y,uu____7526) ->
                          FStar_All.pipe_right bs
                            (FStar_Util.for_some
                               (fun uu____7540  ->
                                  match uu____7540 with
                                  | (x,uu____7546) ->
                                      FStar_Syntax_Syntax.bv_eq x y))))
           in
        let uu____7547 = rank tcenv p  in
        match uu____7547 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____7554 -> true
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
    match projectee with | UDeferred _0 -> true | uu____7581 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____7595 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____7609 -> false
  
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
                        let uu____7661 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____7661 with
                        | (k,uu____7667) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____7677 -> false)))
            | uu____7678 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____7730 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____7736 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____7736 = (Prims.parse_int "0")))
                           in
                        if uu____7730 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____7752 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____7758 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____7758 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____7752)
               in
            let uu____7759 = filter1 u12  in
            let uu____7762 = filter1 u22  in (uu____7759, uu____7762)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____7791 = filter_out_common_univs us1 us2  in
                (match uu____7791 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____7850 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____7850 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____7853 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____7863 =
                          let uu____7864 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____7865 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____7864
                            uu____7865
                           in
                        UFailed uu____7863))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7889 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7889 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7915 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7915 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____7918 ->
                let uu____7923 =
                  let uu____7924 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____7925 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____7924
                    uu____7925 msg
                   in
                UFailed uu____7923
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____7926,uu____7927) ->
              let uu____7928 =
                let uu____7929 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7930 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7929 uu____7930
                 in
              failwith uu____7928
          | (FStar_Syntax_Syntax.U_unknown ,uu____7931) ->
              let uu____7932 =
                let uu____7933 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7934 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7933 uu____7934
                 in
              failwith uu____7932
          | (uu____7935,FStar_Syntax_Syntax.U_bvar uu____7936) ->
              let uu____7937 =
                let uu____7938 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7939 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7938 uu____7939
                 in
              failwith uu____7937
          | (uu____7940,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____7941 =
                let uu____7942 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7943 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7942 uu____7943
                 in
              failwith uu____7941
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____7967 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____7967
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____7981 = occurs_univ v1 u3  in
              if uu____7981
              then
                let uu____7982 =
                  let uu____7983 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7984 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7983 uu____7984
                   in
                try_umax_components u11 u21 uu____7982
              else
                (let uu____7986 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7986)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____7998 = occurs_univ v1 u3  in
              if uu____7998
              then
                let uu____7999 =
                  let uu____8000 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8001 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8000 uu____8001
                   in
                try_umax_components u11 u21 uu____7999
              else
                (let uu____8003 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8003)
          | (FStar_Syntax_Syntax.U_max uu____8004,uu____8005) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8011 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8011
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8013,FStar_Syntax_Syntax.U_max uu____8014) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8020 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8020
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8022,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8023,FStar_Syntax_Syntax.U_name
             uu____8024) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8025) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8026) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8027,FStar_Syntax_Syntax.U_succ
             uu____8028) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8029,FStar_Syntax_Syntax.U_zero
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
      let uu____8129 = bc1  in
      match uu____8129 with
      | (bs1,mk_cod1) ->
          let uu____8173 = bc2  in
          (match uu____8173 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____8284 = aux xs ys  in
                     (match uu____8284 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____8367 =
                       let uu____8374 = mk_cod1 xs  in ([], uu____8374)  in
                     let uu____8377 =
                       let uu____8384 = mk_cod2 ys  in ([], uu____8384)  in
                     (uu____8367, uu____8377)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____8407 'Auu____8408 'Auu____8409 .
    ('Auu____8407,'Auu____8408,'Auu____8409 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___137_8422  ->
    match uu___137_8422 with
    | (uu____8431,uu____8432,[]) -> true
    | uu____8435 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8466 = f  in
      match uu____8466 with
      | (uu____8473,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8474;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8475;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8478;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8479;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8480;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____8532  ->
                 match uu____8532 with
                 | (y,uu____8538) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____8644 =
                  let uu____8653 =
                    let uu____8656 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____8656  in
                  ((FStar_List.rev pat_binders), uu____8653)  in
                FStar_Pervasives_Native.Some uu____8644
            | (uu____8671,[]) ->
                let uu____8694 =
                  let uu____8703 =
                    let uu____8706 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____8706  in
                  ((FStar_List.rev pat_binders), uu____8703)  in
                FStar_Pervasives_Native.Some uu____8694
            | ((formal,uu____8722)::formals1,(a,uu____8725)::args2) ->
                let uu____8759 =
                  let uu____8760 = FStar_Syntax_Subst.compress a  in
                  uu____8760.FStar_Syntax_Syntax.n  in
                (match uu____8759 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____8774 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____8774
                     then
                       let uu____8785 =
                         let uu____8788 =
                           FStar_Syntax_Syntax.mk_binder formal  in
                         uu____8788 :: pat_binders  in
                       aux uu____8785 formals1 t_res args2
                     else
                       (let x1 =
                          let uu___165_8791 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___165_8791.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___165_8791.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____8795 =
                            let uu____8796 =
                              let uu____8803 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____8803)  in
                            FStar_Syntax_Syntax.NT uu____8796  in
                          [uu____8795]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        let uu____8810 =
                          let uu____8813 =
                            FStar_Syntax_Syntax.mk_binder
                              (let uu___166_8816 = x1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_8816.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_8816.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort =
                                   (formal.FStar_Syntax_Syntax.sort)
                               })
                             in
                          uu____8813 :: pat_binders  in
                        aux uu____8810 formals2 t_res1 args2)
                 | uu____8817 ->
                     let uu____8818 =
                       let uu____8821 = FStar_Syntax_Syntax.mk_binder formal
                          in
                       uu____8821 :: pat_binders  in
                     aux uu____8818 formals1 t_res args2)
            | ([],args2) ->
                let uu____8845 =
                  let uu____8858 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____8858  in
                (match uu____8845 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____8909 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____8936 ->
               let uu____8937 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____8937 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9209 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____9209
       then
         let uu____9210 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9210
       else ());
      (let uu____9212 = next_prob probs  in
       match uu____9212 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___167_9239 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___167_9239.wl_deferred);
               ctr = (uu___167_9239.ctr);
               defer_ok = (uu___167_9239.defer_ok);
               smt_ok = (uu___167_9239.smt_ok);
               tcenv = (uu___167_9239.tcenv);
               wl_implicits = (uu___167_9239.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____9246 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____9246
                then
                  let uu____9247 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____9247
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
                          (let uu___168_9252 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___168_9252.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___168_9252.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___168_9252.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___168_9252.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___168_9252.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___168_9252.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___168_9252.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___168_9252.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___168_9252.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9274 ->
                let uu____9283 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9342  ->
                          match uu____9342 with
                          | (c,uu____9350,uu____9351) -> c < probs.ctr))
                   in
                (match uu____9283 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9392 =
                            let uu____9397 =
                              FStar_List.map
                                (fun uu____9412  ->
                                   match uu____9412 with
                                   | (uu____9423,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9397, (probs.wl_implicits))  in
                          Success uu____9392
                      | uu____9426 ->
                          let uu____9435 =
                            let uu___169_9436 = probs  in
                            let uu____9437 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9456  ->
                                      match uu____9456 with
                                      | (uu____9463,uu____9464,y) -> y))
                               in
                            {
                              attempting = uu____9437;
                              wl_deferred = rest;
                              ctr = (uu___169_9436.ctr);
                              defer_ok = (uu___169_9436.defer_ok);
                              smt_ok = (uu___169_9436.smt_ok);
                              tcenv = (uu___169_9436.tcenv);
                              wl_implicits = (uu___169_9436.wl_implicits)
                            }  in
                          solve env uu____9435))))

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
            let uu____9471 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9471 with
            | USolved wl1 ->
                let uu____9473 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9473
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
                  let uu____9525 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____9525 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9528 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9540;
                  FStar_Syntax_Syntax.vars = uu____9541;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9544;
                  FStar_Syntax_Syntax.vars = uu____9545;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9557,uu____9558) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9565,FStar_Syntax_Syntax.Tm_uinst uu____9566) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9573 -> USolved wl

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
            ((let uu____9583 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____9583
              then
                let uu____9584 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9584 msg
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
              let uu____9669 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____9669 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____9721 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____9721
               then
                 let uu____9722 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____9723 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____9722
                   uu____9723
               else ());
              (let uu____9725 = head_matches_delta env1 () t1 t2  in
               match uu____9725 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____9770 ->
                        let uu____9779 = eq_prob t1 t2 wl2  in
                        (match uu____9779 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____9826 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9841 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____9842 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____9841, uu____9842)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9847 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____9848 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____9847, uu____9848)
                           in
                        (match uu____9826 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____9879 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____9879 with
                               | (t1_hd,t1_args) ->
                                   let uu____9918 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____9918 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____9972 =
                                             let uu____9979 =
                                               let uu____9988 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____9988 :: t1_args  in
                                             let uu____10001 =
                                               let uu____10008 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____10008 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____10049  ->
                                                  fun uu____10050  ->
                                                    fun uu____10051  ->
                                                      match (uu____10049,
                                                              uu____10050,
                                                              uu____10051)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____10093),
                                                         (a2,uu____10095)) ->
                                                          let uu____10120 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____10120
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____9979
                                               uu____10001
                                              in
                                           match uu____9972 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___170_10146 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___170_10146.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___170_10146.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10164 =
                                                 solve env1 wl'  in
                                               (match uu____10164 with
                                                | Success (uu____10167,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___171_10171 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___171_10171.attempting);
                                                           wl_deferred =
                                                             (uu___171_10171.wl_deferred);
                                                           ctr =
                                                             (uu___171_10171.ctr);
                                                           defer_ok =
                                                             (uu___171_10171.defer_ok);
                                                           smt_ok =
                                                             (uu___171_10171.smt_ok);
                                                           tcenv =
                                                             (uu___171_10171.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____10182 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____10214 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____10214 with
                               | (t1_base,p1_opt) ->
                                   let uu____10255 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____10255 with
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
                                              let uu____10386 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____10386
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
                                              let uu____10416 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10416
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
                                              let uu____10446 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10446
                                          | uu____10449 -> t_base  in
                                        let uu____10466 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____10466 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____10480 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____10480, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____10487 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____10487 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____10528 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____10528 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____10569 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____10569
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
                             let uu____10593 = combine t11 t21 wl2  in
                             (match uu____10593 with
                              | (t12,ps,wl3) ->
                                  ((let uu____10626 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "RelCheck")
                                       in
                                    if uu____10626
                                    then
                                      let uu____10627 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____10627
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____10666 ts1 =
              match uu____10666 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____10729 = pairwise out t wl2  in
                       (match uu____10729 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____10765 =
              let uu____10776 = FStar_List.hd ts  in (uu____10776, [], wl1)
               in
            let uu____10785 = FStar_List.tl ts  in
            aux uu____10765 uu____10785  in
          let uu____10792 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____10792 with
          | (this_flex,this_rigid) ->
              let uu____10804 =
                let uu____10805 = FStar_Syntax_Subst.compress this_rigid  in
                uu____10805.FStar_Syntax_Syntax.n  in
              (match uu____10804 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____10826 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____10826
                   then
                     let flex = destruct_flex_t this_flex  in
                     let uu____10828 = quasi_pattern env flex  in
                     (match uu____10828 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env
                            "flex-arrow subtyping, not a quasi pattern"
                            (FStar_TypeChecker_Common.TProb tp)
                      | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                          ((let uu____10846 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____10846
                            then
                              let uu____10847 =
                                FStar_Util.string_of_int
                                  tp.FStar_TypeChecker_Common.pid
                                 in
                              FStar_Util.print1
                                "Trying to solve by imitating arrow:%s\n"
                                uu____10847
                            else ());
                           imitate_arrow (FStar_TypeChecker_Common.TProb tp)
                             env wl flex flex_bs flex_t
                             tp.FStar_TypeChecker_Common.relation this_rigid))
                   else
                     solve env
                       (attempt
                          [FStar_TypeChecker_Common.TProb
                             ((let uu___172_10852 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___172_10852.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___172_10852.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___172_10852.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___172_10852.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___172_10852.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___172_10852.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___172_10852.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___172_10852.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___172_10852.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____10853 ->
                   ((let uu____10855 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____10855
                     then
                       let uu____10856 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____10856
                     else ());
                    (let uu____10858 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____10858 with
                     | (u,_args) ->
                         let uu____10895 =
                           let uu____10896 = FStar_Syntax_Subst.compress u
                              in
                           uu____10896.FStar_Syntax_Syntax.n  in
                         (match uu____10895 with
                          | FStar_Syntax_Syntax.Tm_uvar ctx_uvar ->
                              let equiv1 t =
                                let uu____10906 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____10906 with
                                | (u',uu____10922) ->
                                    let uu____10943 =
                                      let uu____10944 = whnf env u'  in
                                      uu____10944.FStar_Syntax_Syntax.n  in
                                    (match uu____10943 with
                                     | FStar_Syntax_Syntax.Tm_uvar ctx_uvar'
                                         ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____10948 -> false)
                                 in
                              let uu____10949 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___138_10972  ->
                                        match uu___138_10972 with
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
                                             | uu____10981 -> false)
                                        | uu____10984 -> false))
                                 in
                              (match uu____10949 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____10998 = whnf env this_rigid
                                        in
                                     let uu____10999 =
                                       FStar_List.collect
                                         (fun uu___139_11005  ->
                                            match uu___139_11005 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____11011 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____11011]
                                            | uu____11013 -> []) bounds_probs
                                        in
                                     uu____10998 :: uu____10999  in
                                   let uu____11014 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____11014 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____11045 =
                                          let uu____11060 =
                                            destruct_flex_t this_flex  in
                                          match uu____11060 with
                                          | (uu____11075,flex_u,uu____11077)
                                              ->
                                              let bound1 =
                                                let uu____11081 =
                                                  let uu____11082 =
                                                    FStar_Syntax_Subst.compress
                                                      bound
                                                     in
                                                  uu____11082.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____11081 with
                                                | FStar_Syntax_Syntax.Tm_refine
                                                    (x,phi) when
                                                    (tp.FStar_TypeChecker_Common.relation
                                                       =
                                                       FStar_TypeChecker_Common.SUB)
                                                      &&
                                                      (let uu____11094 =
                                                         occurs flex_u
                                                           x.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_Pervasives_Native.snd
                                                         uu____11094)
                                                    ->
                                                    x.FStar_Syntax_Syntax.sort
                                                | uu____11103 -> bound  in
                                              let uu____11104 =
                                                new_problem wl1 env bound1
                                                  FStar_TypeChecker_Common.EQ
                                                  this_flex
                                                  FStar_Pervasives_Native.None
                                                  tp.FStar_TypeChecker_Common.loc
                                                  (if flip
                                                   then "joining refinements"
                                                   else "meeting refinements")
                                                 in
                                              (bound1, uu____11104)
                                           in
                                        (match uu____11045 with
                                         | (bound_typ,(eq_prob,wl2)) ->
                                             ((let uu____11150 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "RelCheck")
                                                  in
                                               if uu____11150
                                               then
                                                 let wl' =
                                                   let uu___173_11152 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___173_11152.wl_deferred);
                                                     ctr =
                                                       (uu___173_11152.ctr);
                                                     defer_ok =
                                                       (uu___173_11152.defer_ok);
                                                     smt_ok =
                                                       (uu___173_11152.smt_ok);
                                                     tcenv =
                                                       (uu___173_11152.tcenv);
                                                     wl_implicits =
                                                       (uu___173_11152.wl_implicits)
                                                   }  in
                                                 let uu____11153 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____11153
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11156 =
                                                 solve_t env eq_prob
                                                   (let uu___174_11158 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___174_11158.wl_deferred);
                                                      ctr =
                                                        (uu___174_11158.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___174_11158.smt_ok);
                                                      tcenv =
                                                        (uu___174_11158.tcenv);
                                                      wl_implicits =
                                                        (uu___174_11158.wl_implicits)
                                                    })
                                                  in
                                               match uu____11156 with
                                               | Success uu____11159 ->
                                                   let wl3 =
                                                     let uu___175_11165 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___175_11165.wl_deferred);
                                                       ctr =
                                                         (uu___175_11165.ctr);
                                                       defer_ok =
                                                         (uu___175_11165.defer_ok);
                                                       smt_ok =
                                                         (uu___175_11165.smt_ok);
                                                       tcenv =
                                                         (uu___175_11165.tcenv);
                                                       wl_implicits =
                                                         (uu___175_11165.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____11169 =
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
                                                    (let uu____11181 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "RelCheck")
                                                        in
                                                     if uu____11181
                                                     then
                                                       let uu____11182 =
                                                         let uu____11183 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____11183
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____11182
                                                     else ());
                                                    (let uu____11189 =
                                                       let uu____11204 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____11204)
                                                        in
                                                     match uu____11189 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____11226))
                                                         ->
                                                         let uu____11251 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____11251
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
                                                         let uu____11290 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____11290
                                                          with
                                                          | (eq_prob1,wl3) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl3 tp x
                                                                  phi
                                                                 in
                                                              let wl4 =
                                                                let uu____11307
                                                                  =
                                                                  let uu____11312
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____11312
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____11307
                                                                  [] wl3
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl4))
                                                     | uu____11317 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____11332 when flip ->
                              let uu____11333 =
                                let uu____11334 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a flex-rigid: %s"
                                  uu____11334
                                 in
                              failwith uu____11333
                          | uu____11335 ->
                              let uu____11336 =
                                let uu____11337 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a rigid-flex: %s"
                                  uu____11337
                                 in
                              failwith uu____11336))))

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
                      (fun uu____11365  ->
                         match uu____11365 with
                         | (x,i) ->
                             let uu____11376 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____11376, i)) bs_lhs
                     in
                  let uu____11377 = lhs  in
                  match uu____11377 with
                  | (uu____11378,u_lhs,uu____11380) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____11493 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____11503 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____11503, univ)
                             in
                          match uu____11493 with
                          | (k,univ) ->
                              let uu____11516 =
                                let uu____11523 =
                                  let uu____11526 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____11526
                                   in
                                copy_uvar u_lhs uu____11523 wl2  in
                              (match uu____11516 with
                               | (uu____11539,u,wl3) ->
                                   let uu____11542 =
                                     let uu____11545 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____11545
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____11542, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____11581 =
                              let uu____11594 =
                                let uu____11603 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____11603 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____11649  ->
                                   fun uu____11650  ->
                                     match (uu____11649, uu____11650) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____11741 =
                                           let uu____11748 =
                                             let uu____11751 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____11751
                                              in
                                           copy_uvar u_lhs uu____11748 wl2
                                            in
                                         (match uu____11741 with
                                          | (uu____11774,t_a,wl3) ->
                                              let uu____11777 =
                                                let uu____11784 =
                                                  let uu____11787 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____11787
                                                   in
                                                copy_uvar u_lhs uu____11784
                                                  wl3
                                                 in
                                              (match uu____11777 with
                                               | (uu____11802,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____11594
                                ([], wl1)
                               in
                            (match uu____11581 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___176_11863 = ct  in
                                   let uu____11864 =
                                     let uu____11867 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____11867
                                      in
                                   let uu____11882 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___176_11863.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___176_11863.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____11864;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____11882;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___176_11863.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___177_11900 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___177_11900.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___177_11900.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____11903 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____11903 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____11957 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____11957 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____11974 =
                                          let uu____11979 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____11979)  in
                                        TERM uu____11974  in
                                      let uu____11980 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____11980 with
                                       | (sub_prob,wl3) ->
                                           let uu____11991 =
                                             let uu____11992 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____11992
                                              in
                                           solve env uu____11991))
                             | (x,imp)::formals2 ->
                                 let uu____12006 =
                                   let uu____12013 =
                                     let uu____12016 =
                                       let uu____12019 =
                                         let uu____12020 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____12020
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____12019
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____12016
                                      in
                                   copy_uvar u_lhs uu____12013 wl1  in
                                 (match uu____12006 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____12044 =
                                          let uu____12047 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12047
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12044 t_y
                                         in
                                      let uu____12048 =
                                        let uu____12051 =
                                          let uu____12054 =
                                            let uu____12055 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12055, imp)  in
                                          [uu____12054]  in
                                        FStar_List.append bs_terms
                                          uu____12051
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12048 formals2 wl2)
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
              (let uu____12097 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12097
               then
                 let uu____12098 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12099 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12098 (rel_to_string (p_rel orig)) uu____12099
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____12204 = rhs wl1 scope env1 subst1  in
                     (match uu____12204 with
                      | (rhs_prob,wl2) ->
                          ((let uu____12224 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____12224
                            then
                              let uu____12225 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____12225
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___178_12279 = hd1  in
                       let uu____12280 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___178_12279.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___178_12279.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12280
                       }  in
                     let hd21 =
                       let uu___179_12284 = hd2  in
                       let uu____12285 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___179_12284.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___179_12284.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12285
                       }  in
                     let uu____12288 =
                       let uu____12293 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____12293
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____12288 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____12312 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____12312
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____12316 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____12316 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____12371 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____12371
                                  in
                               ((let uu____12383 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____12383
                                 then
                                   let uu____12384 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____12385 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____12384
                                     uu____12385
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____12412 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____12441 = aux wl [] env [] bs1 bs2  in
               match uu____12441 with
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
        (let uu____12492 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____12492 wl)

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
              let uu____12506 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____12506 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____12536 = lhs1  in
              match uu____12536 with
              | (uu____12539,ctx_u,uu____12541) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____12547 ->
                        let uu____12548 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____12548 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____12595 = quasi_pattern env1 lhs1  in
              match uu____12595 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____12625) ->
                  let uu____12630 = lhs1  in
                  (match uu____12630 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____12644 = occurs_check ctx_u rhs1  in
                       (match uu____12644 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____12686 =
                                let uu____12693 =
                                  let uu____12694 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____12694
                                   in
                                FStar_Util.Inl uu____12693  in
                              (uu____12686, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____12714 =
                                 let uu____12715 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____12715  in
                               if uu____12714
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____12735 =
                                    let uu____12742 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____12742  in
                                  let uu____12747 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____12735, uu____12747)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____12809  ->
                     match uu____12809 with
                     | (x,i) ->
                         let uu____12820 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____12820, i)) bs_lhs
                 in
              let uu____12821 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____12821 with
              | (rhs_hd,args) ->
                  let uu____12858 = FStar_Util.prefix args  in
                  (match uu____12858 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____12916 = lhs1  in
                       (match uu____12916 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____12920 =
                              let uu____12931 =
                                let uu____12938 =
                                  let uu____12941 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____12941
                                   in
                                copy_uvar u_lhs uu____12938 wl1  in
                              match uu____12931 with
                              | (uu____12962,t_last_arg,wl2) ->
                                  let uu____12965 =
                                    let uu____12972 =
                                      let uu____12975 =
                                        let uu____12982 =
                                          let uu____12989 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____12989]  in
                                        FStar_List.append bs_lhs uu____12982
                                         in
                                      let uu____13006 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____12975
                                        uu____13006
                                       in
                                    copy_uvar u_lhs uu____12972 wl2  in
                                  (match uu____12965 with
                                   | (uu____13019,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13025 =
                                         let uu____13032 =
                                           let uu____13035 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____13035
                                            in
                                         copy_uvar u_lhs uu____13032 wl3  in
                                       (match uu____13025 with
                                        | (uu____13048,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____12920 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13072 =
                                     let uu____13073 =
                                       let uu____13078 =
                                         let uu____13079 =
                                           let uu____13082 =
                                             let uu____13087 =
                                               let uu____13088 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13088]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13087
                                              in
                                           uu____13082
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13079
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13078)  in
                                     TERM uu____13073  in
                                   [uu____13072]  in
                                 let uu____13109 =
                                   let uu____13116 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____13116 with
                                   | (p1,wl3) ->
                                       let uu____13133 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____13133 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13109 with
                                  | (sub_probs,wl3) ->
                                      let uu____13160 =
                                        let uu____13161 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____13161  in
                                      solve env1 uu____13160))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____13194 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____13194 with
                | (uu____13209,args) ->
                    (match args with | [] -> false | uu____13237 -> true)
                 in
              let is_arrow rhs2 =
                let uu____13252 =
                  let uu____13253 = FStar_Syntax_Subst.compress rhs2  in
                  uu____13253.FStar_Syntax_Syntax.n  in
                match uu____13252 with
                | FStar_Syntax_Syntax.Tm_arrow uu____13256 -> true
                | uu____13269 -> false  in
              let uu____13270 = quasi_pattern env1 lhs1  in
              match uu____13270 with
              | FStar_Pervasives_Native.None  ->
                  let uu____13281 =
                    let uu____13282 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____13282
                     in
                  giveup_or_defer env1 orig1 wl1 uu____13281
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____13289 = is_app rhs1  in
                  if uu____13289
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____13291 = is_arrow rhs1  in
                     if uu____13291
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____13293 =
                          let uu____13294 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____13294
                           in
                        giveup_or_defer env1 orig1 wl1 uu____13293))
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
                let uu____13297 = lhs  in
                (match uu____13297 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____13301 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____13301 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____13316 =
                              let uu____13319 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____13319
                               in
                            FStar_All.pipe_right uu____13316
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____13334 = occurs_check ctx_uv rhs1  in
                          (match uu____13334 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____13356 =
                                   let uu____13357 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____13357
                                    in
                                 giveup_or_defer env orig wl uu____13356
                               else
                                 (let uu____13359 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____13359
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____13364 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____13364
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____13366 =
                                         let uu____13367 =
                                           names_to_string1 fvs2  in
                                         let uu____13368 =
                                           names_to_string1 fvs1  in
                                         let uu____13369 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____13367 uu____13368
                                           uu____13369
                                          in
                                       giveup_or_defer env orig wl
                                         uu____13366)
                                    else first_order orig env wl lhs rhs1))
                      | uu____13375 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____13379 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____13379 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____13402 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____13402
                             | (FStar_Util.Inl msg,uu____13404) ->
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
                  (let uu____13433 =
                     let uu____13450 = quasi_pattern env lhs  in
                     let uu____13457 = quasi_pattern env rhs  in
                     (uu____13450, uu____13457)  in
                   match uu____13433 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____13500 = lhs  in
                       (match uu____13500 with
                        | ({ FStar_Syntax_Syntax.n = uu____13501;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____13503;_},u_lhs,uu____13505)
                            ->
                            let uu____13508 = rhs  in
                            (match uu____13508 with
                             | (uu____13509,u_rhs,uu____13511) ->
                                 let uu____13512 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____13512
                                 then
                                   let uu____13513 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____13513
                                 else
                                   (let uu____13515 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____13515 with
                                    | (sub_prob,wl1) ->
                                        let uu____13526 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____13526 with
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
                                             let uu____13554 =
                                               let uu____13561 =
                                                 let uu____13564 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____13564
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi: lhs="
                                                    (Prims.strcat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.strcat ", rhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))
                                                 wl1 range gamma_w ctx_w
                                                 uu____13561
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____13554 with
                                              | (uu____13567,w,wl2) ->
                                                  let w_app =
                                                    let uu____13573 =
                                                      let uu____13578 =
                                                        FStar_List.map
                                                          (fun uu____13587 
                                                             ->
                                                             match uu____13587
                                                             with
                                                             | (z,uu____13593)
                                                                 ->
                                                                 let uu____13594
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____13594)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____13578
                                                       in
                                                    uu____13573
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____13598 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "RelCheck")
                                                       in
                                                    if uu____13598
                                                    then
                                                      let uu____13599 =
                                                        flex_t_to_string lhs
                                                         in
                                                      let uu____13600 =
                                                        flex_t_to_string rhs
                                                         in
                                                      let uu____13601 =
                                                        let uu____13602 =
                                                          destruct_flex_t w
                                                           in
                                                        flex_t_to_string
                                                          uu____13602
                                                         in
                                                      FStar_Util.print3
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s"
                                                        uu____13599
                                                        uu____13600
                                                        uu____13601
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____13614 =
                                                          let uu____13619 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____13619)
                                                           in
                                                        TERM uu____13614  in
                                                      let uu____13620 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____13620
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____13625 =
                                                             let uu____13630
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
                                                               uu____13630)
                                                              in
                                                           TERM uu____13625
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____13631 =
                                                      let uu____13632 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____13632
                                                       in
                                                    solve env uu____13631)))))))
                   | uu____13633 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____13701 = head_matches_delta env1 wl1 t1 t2  in
           match uu____13701 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____13732,uu____13733) ->
                    let rec may_relate head3 =
                      let uu____13760 =
                        let uu____13761 = FStar_Syntax_Subst.compress head3
                           in
                        uu____13761.FStar_Syntax_Syntax.n  in
                      match uu____13760 with
                      | FStar_Syntax_Syntax.Tm_name uu____13764 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____13765 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13788;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____13789;
                            FStar_Syntax_Syntax.fv_qual = uu____13790;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13793;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____13794;
                            FStar_Syntax_Syntax.fv_qual = uu____13795;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____13799,uu____13800) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____13842) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____13848) ->
                          may_relate t
                      | uu____13853 -> false  in
                    let uu____13854 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____13854
                    then
                      let uu____13855 =
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
                                 let uu____13887 =
                                   let uu____13888 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____13888 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____13887
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____13893 = has_type_guard t1 t2  in
                             (uu____13893, wl1)
                           else
                             (let uu____13899 = has_type_guard t2 t1  in
                              (uu____13899, wl1)))
                         in
                      (match uu____13855 with
                       | (guard,wl2) ->
                           let uu____13906 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____13906)
                    else
                      (let uu____13908 =
                         let uu____13909 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13910 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____13909 uu____13910
                          in
                       giveup env1 uu____13908 orig)
                | (uu____13911,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___180_13925 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___180_13925.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___180_13925.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___180_13925.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___180_13925.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___180_13925.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___180_13925.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___180_13925.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___180_13925.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____13926,FStar_Pervasives_Native.None ) ->
                    ((let uu____13938 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13938
                      then
                        let uu____13939 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____13940 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____13941 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____13942 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____13939 uu____13940 uu____13941 uu____13942
                      else ());
                     (let uu____13944 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____13944 with
                      | (head11,args1) ->
                          let uu____13981 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____13981 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____14035 =
                                   let uu____14036 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____14037 = args_to_string args1  in
                                   let uu____14038 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____14039 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____14036 uu____14037 uu____14038
                                     uu____14039
                                    in
                                 giveup env1 uu____14035 orig
                               else
                                 (let uu____14041 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____14048 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____14048 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____14041
                                  then
                                    let uu____14049 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____14049 with
                                    | USolved wl2 ->
                                        let uu____14051 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____14051
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____14055 =
                                       base_and_refinement env1 t1  in
                                     match uu____14055 with
                                     | (base1,refinement1) ->
                                         let uu____14080 =
                                           base_and_refinement env1 t2  in
                                         (match uu____14080 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____14137 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____14137 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____14141 =
                                                          FStar_List.fold_right2
                                                            (fun uu____14174 
                                                               ->
                                                               fun
                                                                 uu____14175 
                                                                 ->
                                                                 fun
                                                                   uu____14176
                                                                    ->
                                                                   match 
                                                                    (uu____14174,
                                                                    uu____14175,
                                                                    uu____14176)
                                                                   with
                                                                   | 
                                                                   ((a,uu____14212),
                                                                    (a',uu____14214),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____14235
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____14235
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
                                                        (match uu____14141
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____14263
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____14263
                                                               then
                                                                 let uu____14264
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____14264
                                                               else ());
                                                              (let formula =
                                                                 let uu____14269
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____14269
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
                                               | uu____14277 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___181_14317 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___181_14317.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____14320 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____14320
          then
            let uu____14321 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____14321
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____14326 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "RelCheck")
                 in
              if uu____14326
              then
                let uu____14327 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____14328 =
                  let uu____14329 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____14330 =
                    let uu____14331 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____14331  in
                  Prims.strcat uu____14329 uu____14330  in
                let uu____14332 =
                  let uu____14333 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____14334 =
                    let uu____14335 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____14335  in
                  Prims.strcat uu____14333 uu____14334  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____14327
                  uu____14328 uu____14332
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____14338,uu____14339) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____14364,FStar_Syntax_Syntax.Tm_delayed uu____14365) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____14390,uu____14391) ->
                  let uu____14418 =
                    let uu___182_14419 = problem  in
                    let uu____14420 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___182_14419.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____14420;
                      FStar_TypeChecker_Common.relation =
                        (uu___182_14419.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___182_14419.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___182_14419.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___182_14419.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___182_14419.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___182_14419.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___182_14419.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___182_14419.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14418 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____14421,uu____14422) ->
                  let uu____14429 =
                    let uu___183_14430 = problem  in
                    let uu____14431 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___183_14430.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____14431;
                      FStar_TypeChecker_Common.relation =
                        (uu___183_14430.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___183_14430.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___183_14430.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___183_14430.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___183_14430.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___183_14430.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___183_14430.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___183_14430.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14429 wl
              | (uu____14432,FStar_Syntax_Syntax.Tm_ascribed uu____14433) ->
                  let uu____14460 =
                    let uu___184_14461 = problem  in
                    let uu____14462 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___184_14461.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___184_14461.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___184_14461.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____14462;
                      FStar_TypeChecker_Common.element =
                        (uu___184_14461.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___184_14461.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___184_14461.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___184_14461.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___184_14461.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___184_14461.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14460 wl
              | (uu____14463,FStar_Syntax_Syntax.Tm_meta uu____14464) ->
                  let uu____14471 =
                    let uu___185_14472 = problem  in
                    let uu____14473 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___185_14472.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___185_14472.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___185_14472.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____14473;
                      FStar_TypeChecker_Common.element =
                        (uu___185_14472.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___185_14472.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___185_14472.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___185_14472.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___185_14472.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___185_14472.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14471 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____14475),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____14477)) ->
                  let uu____14486 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____14486
              | (FStar_Syntax_Syntax.Tm_bvar uu____14487,uu____14488) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____14489,FStar_Syntax_Syntax.Tm_bvar uu____14490) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___140_14549 =
                    match uu___140_14549 with
                    | [] -> c
                    | bs ->
                        let uu____14571 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____14571
                     in
                  let uu____14580 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____14580 with
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
                                    let uu____14703 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____14703
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
                  let mk_t t l uu___141_14778 =
                    match uu___141_14778 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____14812 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____14812 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____14931 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____14932 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____14931
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____14932 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____14933,uu____14934) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____14961 -> true
                    | uu____14978 -> false  in
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
                      (let uu____15019 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___186_15027 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___186_15027.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___186_15027.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___186_15027.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___186_15027.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___186_15027.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___186_15027.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___186_15027.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___186_15027.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___186_15027.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___186_15027.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___186_15027.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___186_15027.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___186_15027.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___186_15027.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___186_15027.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___186_15027.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___186_15027.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___186_15027.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___186_15027.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___186_15027.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___186_15027.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___186_15027.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___186_15027.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___186_15027.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___186_15027.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___186_15027.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___186_15027.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___186_15027.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___186_15027.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___186_15027.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___186_15027.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___186_15027.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___186_15027.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___186_15027.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___186_15027.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15019 with
                       | (uu____15030,ty,uu____15032) ->
                           let uu____15033 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15033)
                     in
                  let uu____15034 =
                    let uu____15047 = maybe_eta t1  in
                    let uu____15052 = maybe_eta t2  in
                    (uu____15047, uu____15052)  in
                  (match uu____15034 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___187_15076 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___187_15076.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___187_15076.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___187_15076.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___187_15076.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___187_15076.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___187_15076.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___187_15076.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___187_15076.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15087 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15087
                       then
                         let uu____15088 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____15088 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_15097 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_15097.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_15097.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_15097.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_15097.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_15097.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_15097.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_15097.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_15097.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____15109 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15109
                       then
                         let uu____15110 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____15110 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_15119 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_15119.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_15119.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_15119.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_15119.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_15119.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_15119.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_15119.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_15119.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____15121 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____15134,FStar_Syntax_Syntax.Tm_abs uu____15135) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15162 -> true
                    | uu____15179 -> false  in
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
                      (let uu____15220 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___186_15228 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___186_15228.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___186_15228.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___186_15228.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___186_15228.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___186_15228.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___186_15228.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___186_15228.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___186_15228.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___186_15228.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___186_15228.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___186_15228.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___186_15228.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___186_15228.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___186_15228.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___186_15228.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___186_15228.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___186_15228.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___186_15228.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___186_15228.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___186_15228.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___186_15228.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___186_15228.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___186_15228.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___186_15228.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___186_15228.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___186_15228.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___186_15228.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___186_15228.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___186_15228.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___186_15228.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___186_15228.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___186_15228.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___186_15228.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___186_15228.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___186_15228.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15220 with
                       | (uu____15231,ty,uu____15233) ->
                           let uu____15234 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15234)
                     in
                  let uu____15235 =
                    let uu____15248 = maybe_eta t1  in
                    let uu____15253 = maybe_eta t2  in
                    (uu____15248, uu____15253)  in
                  (match uu____15235 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___187_15277 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___187_15277.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___187_15277.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___187_15277.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___187_15277.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___187_15277.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___187_15277.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___187_15277.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___187_15277.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15288 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15288
                       then
                         let uu____15289 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____15289 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_15298 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_15298.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_15298.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_15298.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_15298.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_15298.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_15298.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_15298.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_15298.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____15310 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15310
                       then
                         let uu____15311 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____15311 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___188_15320 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___188_15320.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___188_15320.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___188_15320.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___188_15320.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___188_15320.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___188_15320.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___188_15320.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___188_15320.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____15322 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____15350 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____15350) &&
                       (let uu____15354 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____15354))
                      &&
                      (let uu____15361 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____15361 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___142_15373 =
                             match uu___142_15373 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____15374 -> true
                             | uu____15375 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____15376 -> false)
                     in
                  let uu____15377 = as_refinement should_delta env wl t1  in
                  (match uu____15377 with
                   | (x11,phi1) ->
                       let uu____15384 = as_refinement should_delta env wl t2
                          in
                       (match uu____15384 with
                        | (x21,phi21) ->
                            let uu____15391 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____15391 with
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
                                   let uu____15457 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____15457
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____15469 =
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
                                   let uu____15480 =
                                     let uu____15485 =
                                       let uu____15492 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____15492]  in
                                     mk_t_problem wl1 uu____15485 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____15480 with
                                    | (ref_prob,wl2) ->
                                        let uu____15507 =
                                          solve env1
                                            (let uu___189_15509 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___189_15509.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___189_15509.smt_ok);
                                               tcenv = (uu___189_15509.tcenv);
                                               wl_implicits =
                                                 (uu___189_15509.wl_implicits)
                                             })
                                           in
                                        (match uu____15507 with
                                         | Failed uu____15516 -> fallback ()
                                         | Success uu____15521 ->
                                             let guard =
                                               let uu____15529 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____15529
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___190_15538 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___190_15538.attempting);
                                                 wl_deferred =
                                                   (uu___190_15538.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___190_15538.defer_ok);
                                                 smt_ok =
                                                   (uu___190_15538.smt_ok);
                                                 tcenv =
                                                   (uu___190_15538.tcenv);
                                                 wl_implicits =
                                                   (uu___190_15538.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15540,FStar_Syntax_Syntax.Tm_uvar uu____15541) ->
                  let uu____15542 = destruct_flex_t t1  in
                  let uu____15543 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15542 uu____15543
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15544;
                    FStar_Syntax_Syntax.pos = uu____15545;
                    FStar_Syntax_Syntax.vars = uu____15546;_},uu____15547),FStar_Syntax_Syntax.Tm_uvar
                 uu____15548) ->
                  let uu____15569 = destruct_flex_t t1  in
                  let uu____15570 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15569 uu____15570
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15571,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15572;
                    FStar_Syntax_Syntax.pos = uu____15573;
                    FStar_Syntax_Syntax.vars = uu____15574;_},uu____15575))
                  ->
                  let uu____15596 = destruct_flex_t t1  in
                  let uu____15597 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15596 uu____15597
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15598;
                    FStar_Syntax_Syntax.pos = uu____15599;
                    FStar_Syntax_Syntax.vars = uu____15600;_},uu____15601),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15602;
                    FStar_Syntax_Syntax.pos = uu____15603;
                    FStar_Syntax_Syntax.vars = uu____15604;_},uu____15605))
                  ->
                  let uu____15646 = destruct_flex_t t1  in
                  let uu____15647 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15646 uu____15647
              | (FStar_Syntax_Syntax.Tm_uvar uu____15648,uu____15649) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____15650 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____15650 t2
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15651;
                    FStar_Syntax_Syntax.pos = uu____15652;
                    FStar_Syntax_Syntax.vars = uu____15653;_},uu____15654),uu____15655)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____15676 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____15676 t2
              | (uu____15677,FStar_Syntax_Syntax.Tm_uvar uu____15678) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____15679,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15680;
                    FStar_Syntax_Syntax.pos = uu____15681;
                    FStar_Syntax_Syntax.vars = uu____15682;_},uu____15683))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15704,FStar_Syntax_Syntax.Tm_arrow uu____15705) ->
                  solve_t' env
                    (let uu___191_15719 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___191_15719.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___191_15719.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___191_15719.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___191_15719.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___191_15719.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___191_15719.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___191_15719.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___191_15719.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___191_15719.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15720;
                    FStar_Syntax_Syntax.pos = uu____15721;
                    FStar_Syntax_Syntax.vars = uu____15722;_},uu____15723),FStar_Syntax_Syntax.Tm_arrow
                 uu____15724) ->
                  solve_t' env
                    (let uu___191_15758 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___191_15758.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___191_15758.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___191_15758.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___191_15758.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___191_15758.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___191_15758.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___191_15758.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___191_15758.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___191_15758.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____15759,FStar_Syntax_Syntax.Tm_uvar uu____15760) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____15761,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15762;
                    FStar_Syntax_Syntax.pos = uu____15763;
                    FStar_Syntax_Syntax.vars = uu____15764;_},uu____15765))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____15786,uu____15787) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15788;
                    FStar_Syntax_Syntax.pos = uu____15789;
                    FStar_Syntax_Syntax.vars = uu____15790;_},uu____15791),uu____15792)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____15813,uu____15814) ->
                  let t21 =
                    let uu____15822 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____15822  in
                  solve_t env
                    (let uu___192_15848 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___192_15848.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___192_15848.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___192_15848.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___192_15848.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___192_15848.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___192_15848.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___192_15848.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___192_15848.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___192_15848.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____15849,FStar_Syntax_Syntax.Tm_refine uu____15850) ->
                  let t11 =
                    let uu____15858 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____15858  in
                  solve_t env
                    (let uu___193_15884 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___193_15884.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___193_15884.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___193_15884.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___193_15884.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___193_15884.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___193_15884.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___193_15884.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___193_15884.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___193_15884.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____15961 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____15961 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____16182 = br1  in
                             (match uu____16182 with
                              | (p1,w1,uu____16207) ->
                                  let uu____16224 = br2  in
                                  (match uu____16224 with
                                   | (p2,w2,uu____16243) ->
                                       let uu____16248 =
                                         let uu____16249 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____16249  in
                                       if uu____16248
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____16265 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____16265 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____16298 = br2  in
                                              (match uu____16298 with
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
                                                     let uu____16333 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____16333
                                                      in
                                                   let uu____16344 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____16367,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____16384) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____16427 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____16427
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____16344
                                                     (fun uu____16469  ->
                                                        match uu____16469
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____16490 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____16490
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____16505
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____16505
                                                                   (fun
                                                                    uu____16529
                                                                     ->
                                                                    match uu____16529
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
                         | uu____16614 -> FStar_Pervasives_Native.None  in
                       let uu____16651 = solve_branches wl1 brs1 brs2  in
                       (match uu____16651 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____16682,uu____16683) ->
                  let head1 =
                    let uu____16707 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16707
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16747 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16747
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16787 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16787
                    then
                      let uu____16788 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16789 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16790 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16788 uu____16789 uu____16790
                    else ());
                   (let uu____16792 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16792
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16799 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16799
                       then
                         let uu____16800 =
                           let uu____16807 =
                             let uu____16808 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16808 = FStar_Syntax_Util.Equal  in
                           if uu____16807
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16818 = mk_eq2 wl orig t1 t2  in
                              match uu____16818 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16800 with
                         | (guard,wl1) ->
                             let uu____16839 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16839
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____16842,uu____16843) ->
                  let head1 =
                    let uu____16851 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16851
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16891 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16891
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16931 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16931
                    then
                      let uu____16932 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16933 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16934 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16932 uu____16933 uu____16934
                    else ());
                   (let uu____16936 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16936
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16943 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16943
                       then
                         let uu____16944 =
                           let uu____16951 =
                             let uu____16952 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16952 = FStar_Syntax_Util.Equal  in
                           if uu____16951
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16962 = mk_eq2 wl orig t1 t2  in
                              match uu____16962 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16944 with
                         | (guard,wl1) ->
                             let uu____16983 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16983
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____16986,uu____16987) ->
                  let head1 =
                    let uu____16989 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16989
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17029 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17029
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17069 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17069
                    then
                      let uu____17070 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17071 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17072 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17070 uu____17071 uu____17072
                    else ());
                   (let uu____17074 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17074
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17081 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17081
                       then
                         let uu____17082 =
                           let uu____17089 =
                             let uu____17090 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17090 = FStar_Syntax_Util.Equal  in
                           if uu____17089
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17100 = mk_eq2 wl orig t1 t2  in
                              match uu____17100 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17082 with
                         | (guard,wl1) ->
                             let uu____17121 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17121
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____17124,uu____17125) ->
                  let head1 =
                    let uu____17127 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17127
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17167 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17167
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17207 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17207
                    then
                      let uu____17208 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17209 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17210 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17208 uu____17209 uu____17210
                    else ());
                   (let uu____17212 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17212
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17219 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17219
                       then
                         let uu____17220 =
                           let uu____17227 =
                             let uu____17228 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17228 = FStar_Syntax_Util.Equal  in
                           if uu____17227
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17238 = mk_eq2 wl orig t1 t2  in
                              match uu____17238 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17220 with
                         | (guard,wl1) ->
                             let uu____17259 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17259
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____17262,uu____17263) ->
                  let head1 =
                    let uu____17265 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17265
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17305 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17305
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17345 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17345
                    then
                      let uu____17346 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17347 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17348 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17346 uu____17347 uu____17348
                    else ());
                   (let uu____17350 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17350
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17357 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17357
                       then
                         let uu____17358 =
                           let uu____17365 =
                             let uu____17366 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17366 = FStar_Syntax_Util.Equal  in
                           if uu____17365
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17376 = mk_eq2 wl orig t1 t2  in
                              match uu____17376 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17358 with
                         | (guard,wl1) ->
                             let uu____17397 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17397
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____17400,uu____17401) ->
                  let head1 =
                    let uu____17417 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17417
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17457 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17457
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17497 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17497
                    then
                      let uu____17498 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17499 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17500 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17498 uu____17499 uu____17500
                    else ());
                   (let uu____17502 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17502
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17509 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17509
                       then
                         let uu____17510 =
                           let uu____17517 =
                             let uu____17518 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17518 = FStar_Syntax_Util.Equal  in
                           if uu____17517
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17528 = mk_eq2 wl orig t1 t2  in
                              match uu____17528 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17510 with
                         | (guard,wl1) ->
                             let uu____17549 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17549
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17552,FStar_Syntax_Syntax.Tm_match uu____17553) ->
                  let head1 =
                    let uu____17577 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17577
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17617 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17617
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17657 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17657
                    then
                      let uu____17658 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17659 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17660 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17658 uu____17659 uu____17660
                    else ());
                   (let uu____17662 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17662
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17669 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17669
                       then
                         let uu____17670 =
                           let uu____17677 =
                             let uu____17678 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17678 = FStar_Syntax_Util.Equal  in
                           if uu____17677
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17688 = mk_eq2 wl orig t1 t2  in
                              match uu____17688 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17670 with
                         | (guard,wl1) ->
                             let uu____17709 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17709
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17712,FStar_Syntax_Syntax.Tm_uinst uu____17713) ->
                  let head1 =
                    let uu____17721 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17721
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17761 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17761
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17801 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17801
                    then
                      let uu____17802 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17803 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17804 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17802 uu____17803 uu____17804
                    else ());
                   (let uu____17806 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17806
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17813 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17813
                       then
                         let uu____17814 =
                           let uu____17821 =
                             let uu____17822 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17822 = FStar_Syntax_Util.Equal  in
                           if uu____17821
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17832 = mk_eq2 wl orig t1 t2  in
                              match uu____17832 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17814 with
                         | (guard,wl1) ->
                             let uu____17853 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17853
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17856,FStar_Syntax_Syntax.Tm_name uu____17857) ->
                  let head1 =
                    let uu____17859 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17859
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17899 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17899
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17939 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17939
                    then
                      let uu____17940 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17941 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17942 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17940 uu____17941 uu____17942
                    else ());
                   (let uu____17944 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17944
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17951 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17951
                       then
                         let uu____17952 =
                           let uu____17959 =
                             let uu____17960 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17960 = FStar_Syntax_Util.Equal  in
                           if uu____17959
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17970 = mk_eq2 wl orig t1 t2  in
                              match uu____17970 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17952 with
                         | (guard,wl1) ->
                             let uu____17991 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17991
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17994,FStar_Syntax_Syntax.Tm_constant uu____17995) ->
                  let head1 =
                    let uu____17997 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17997
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18037 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18037
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18077 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____18077
                    then
                      let uu____18078 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18079 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18080 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18078 uu____18079 uu____18080
                    else ());
                   (let uu____18082 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18082
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18089 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18089
                       then
                         let uu____18090 =
                           let uu____18097 =
                             let uu____18098 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18098 = FStar_Syntax_Util.Equal  in
                           if uu____18097
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18108 = mk_eq2 wl orig t1 t2  in
                              match uu____18108 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18090 with
                         | (guard,wl1) ->
                             let uu____18129 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18129
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18132,FStar_Syntax_Syntax.Tm_fvar uu____18133) ->
                  let head1 =
                    let uu____18135 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18135
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18175 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18175
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18215 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____18215
                    then
                      let uu____18216 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18217 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18218 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18216 uu____18217 uu____18218
                    else ());
                   (let uu____18220 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18220
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18227 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18227
                       then
                         let uu____18228 =
                           let uu____18235 =
                             let uu____18236 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18236 = FStar_Syntax_Util.Equal  in
                           if uu____18235
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18246 = mk_eq2 wl orig t1 t2  in
                              match uu____18246 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18228 with
                         | (guard,wl1) ->
                             let uu____18267 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18267
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18270,FStar_Syntax_Syntax.Tm_app uu____18271) ->
                  let head1 =
                    let uu____18287 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18287
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18327 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18327
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18367 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____18367
                    then
                      let uu____18368 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18369 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18370 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18368 uu____18369 uu____18370
                    else ());
                   (let uu____18372 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18372
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18379 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18379
                       then
                         let uu____18380 =
                           let uu____18387 =
                             let uu____18388 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18388 = FStar_Syntax_Util.Equal  in
                           if uu____18387
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18398 = mk_eq2 wl orig t1 t2  in
                              match uu____18398 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18380 with
                         | (guard,wl1) ->
                             let uu____18419 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18419
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____18422,FStar_Syntax_Syntax.Tm_let uu____18423) ->
                  let uu____18448 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____18448
                  then
                    let uu____18449 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____18449
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____18451,uu____18452) ->
                  let uu____18465 =
                    let uu____18470 =
                      let uu____18471 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____18472 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____18473 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____18474 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____18471 uu____18472 uu____18473 uu____18474
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____18470)
                     in
                  FStar_Errors.raise_error uu____18465
                    t1.FStar_Syntax_Syntax.pos
              | (uu____18475,FStar_Syntax_Syntax.Tm_let uu____18476) ->
                  let uu____18489 =
                    let uu____18494 =
                      let uu____18495 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____18496 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____18497 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____18498 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____18495 uu____18496 uu____18497 uu____18498
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____18494)
                     in
                  FStar_Errors.raise_error uu____18489
                    t1.FStar_Syntax_Syntax.pos
              | uu____18499 -> giveup env "head tag mismatch" orig))))

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
          (let uu____18558 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____18558
           then
             let uu____18559 =
               let uu____18560 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____18560  in
             let uu____18561 =
               let uu____18562 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____18562  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____18559 uu____18561
           else ());
          (let uu____18564 =
             let uu____18565 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____18565  in
           if uu____18564
           then
             let uu____18566 =
               let uu____18567 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____18568 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____18567 uu____18568
                in
             giveup env uu____18566 orig
           else
             (let uu____18570 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____18570 with
              | (ret_sub_prob,wl1) ->
                  let uu____18577 =
                    FStar_List.fold_right2
                      (fun uu____18610  ->
                         fun uu____18611  ->
                           fun uu____18612  ->
                             match (uu____18610, uu____18611, uu____18612)
                             with
                             | ((a1,uu____18648),(a2,uu____18650),(arg_sub_probs,wl2))
                                 ->
                                 let uu____18671 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____18671 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____18577 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____18700 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____18700  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____18730 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____18733)::[] -> wp1
              | uu____18750 ->
                  let uu____18759 =
                    let uu____18760 =
                      let uu____18761 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____18761  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____18760
                     in
                  failwith uu____18759
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____18767 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____18767]
              | x -> x  in
            let uu____18769 =
              let uu____18778 =
                let uu____18785 =
                  let uu____18786 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____18786 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____18785  in
              [uu____18778]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____18769;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____18799 = lift_c1 ()  in solve_eq uu____18799 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___143_18805  ->
                       match uu___143_18805 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____18806 -> false))
                in
             let uu____18807 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____18833)::uu____18834,(wp2,uu____18836)::uu____18837)
                   -> (wp1, wp2)
               | uu____18890 ->
                   let uu____18911 =
                     let uu____18916 =
                       let uu____18917 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____18918 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____18917 uu____18918
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____18916)
                      in
                   FStar_Errors.raise_error uu____18911
                     env.FStar_TypeChecker_Env.range
                in
             match uu____18807 with
             | (wpc1,wpc2) ->
                 let uu____18925 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____18925
                 then
                   let uu____18928 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____18928 wl
                 else
                   (let uu____18930 =
                      let uu____18937 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____18937  in
                    match uu____18930 with
                    | (c2_decl,qualifiers) ->
                        let uu____18958 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____18958
                        then
                          let c1_repr =
                            let uu____18962 =
                              let uu____18963 =
                                let uu____18964 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____18964  in
                              let uu____18965 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____18963 uu____18965
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____18962
                             in
                          let c2_repr =
                            let uu____18967 =
                              let uu____18968 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____18969 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____18968 uu____18969
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____18967
                             in
                          let uu____18970 =
                            let uu____18975 =
                              let uu____18976 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____18977 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____18976 uu____18977
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____18975
                             in
                          (match uu____18970 with
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
                                 ((let uu____18991 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____18991
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____18994 =
                                     let uu____19001 =
                                       let uu____19002 =
                                         let uu____19017 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____19020 =
                                           let uu____19029 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____19036 =
                                             let uu____19045 =
                                               let uu____19052 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____19052
                                                in
                                             [uu____19045]  in
                                           uu____19029 :: uu____19036  in
                                         (uu____19017, uu____19020)  in
                                       FStar_Syntax_Syntax.Tm_app uu____19002
                                        in
                                     FStar_Syntax_Syntax.mk uu____19001  in
                                   uu____18994 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____19087 =
                                    let uu____19094 =
                                      let uu____19095 =
                                        let uu____19110 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____19113 =
                                          let uu____19122 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____19129 =
                                            let uu____19138 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____19145 =
                                              let uu____19154 =
                                                let uu____19161 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____19161
                                                 in
                                              [uu____19154]  in
                                            uu____19138 :: uu____19145  in
                                          uu____19122 :: uu____19129  in
                                        (uu____19110, uu____19113)  in
                                      FStar_Syntax_Syntax.Tm_app uu____19095
                                       in
                                    FStar_Syntax_Syntax.mk uu____19094  in
                                  uu____19087 FStar_Pervasives_Native.None r)
                              in
                           let uu____19199 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____19199 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____19207 =
                                   let uu____19210 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____19210
                                    in
                                 solve_prob orig uu____19207 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____19217 = FStar_Util.physical_equality c1 c2  in
        if uu____19217
        then
          let uu____19218 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____19218
        else
          ((let uu____19221 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____19221
            then
              let uu____19222 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____19223 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____19222
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____19223
            else ());
           (let uu____19225 =
              let uu____19234 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____19237 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____19234, uu____19237)  in
            match uu____19225 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____19255),FStar_Syntax_Syntax.Total
                    (t2,uu____19257)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____19274 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____19274 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____19275,FStar_Syntax_Syntax.Total uu____19276) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____19294),FStar_Syntax_Syntax.Total
                    (t2,uu____19296)) ->
                     let uu____19313 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____19313 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____19315),FStar_Syntax_Syntax.GTotal
                    (t2,uu____19317)) ->
                     let uu____19334 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____19334 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____19336),FStar_Syntax_Syntax.GTotal
                    (t2,uu____19338)) ->
                     let uu____19355 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____19355 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____19356,FStar_Syntax_Syntax.Comp uu____19357) ->
                     let uu____19366 =
                       let uu___194_19369 = problem  in
                       let uu____19372 =
                         let uu____19373 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19373
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___194_19369.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____19372;
                         FStar_TypeChecker_Common.relation =
                           (uu___194_19369.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___194_19369.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___194_19369.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___194_19369.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___194_19369.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___194_19369.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___194_19369.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___194_19369.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19366 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____19374,FStar_Syntax_Syntax.Comp uu____19375) ->
                     let uu____19384 =
                       let uu___194_19387 = problem  in
                       let uu____19390 =
                         let uu____19391 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19391
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___194_19387.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____19390;
                         FStar_TypeChecker_Common.relation =
                           (uu___194_19387.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___194_19387.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___194_19387.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___194_19387.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___194_19387.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___194_19387.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___194_19387.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___194_19387.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19384 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____19392,FStar_Syntax_Syntax.GTotal uu____19393) ->
                     let uu____19402 =
                       let uu___195_19405 = problem  in
                       let uu____19408 =
                         let uu____19409 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19409
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___195_19405.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___195_19405.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___195_19405.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____19408;
                         FStar_TypeChecker_Common.element =
                           (uu___195_19405.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___195_19405.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___195_19405.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___195_19405.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___195_19405.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___195_19405.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19402 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____19410,FStar_Syntax_Syntax.Total uu____19411) ->
                     let uu____19420 =
                       let uu___195_19423 = problem  in
                       let uu____19426 =
                         let uu____19427 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____19427
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___195_19423.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___195_19423.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___195_19423.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____19426;
                         FStar_TypeChecker_Common.element =
                           (uu___195_19423.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___195_19423.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___195_19423.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___195_19423.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___195_19423.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___195_19423.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____19420 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____19428,FStar_Syntax_Syntax.Comp uu____19429) ->
                     let uu____19430 =
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
                     if uu____19430
                     then
                       let uu____19431 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____19431 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____19435 =
                            let uu____19440 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____19440
                            then (c1_comp, c2_comp)
                            else
                              (let uu____19446 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____19447 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____19446, uu____19447))
                             in
                          match uu____19435 with
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
                           (let uu____19454 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____19454
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____19456 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____19456 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____19459 =
                                  let uu____19460 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____19461 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____19460 uu____19461
                                   in
                                giveup env uu____19459 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____19468 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____19501  ->
              match uu____19501 with
              | (uu____19512,tm,uu____19514,uu____19515,uu____19516) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____19468 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____19549 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____19549 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____19567 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____19595  ->
                match uu____19595 with
                | (u1,u2) ->
                    let uu____19602 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____19603 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____19602 uu____19603))
         in
      FStar_All.pipe_right uu____19567 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____19630,[])) -> "{}"
      | uu____19655 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____19678 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____19678
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____19681 =
              FStar_List.map
                (fun uu____19691  ->
                   match uu____19691 with
                   | (uu____19696,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____19681 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____19701 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____19701 imps
  
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
                  let uu____19754 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ExplainRel")
                     in
                  if uu____19754
                  then
                    let uu____19755 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____19756 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____19755
                      (rel_to_string rel) uu____19756
                  else "TOP"  in
                let uu____19758 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____19758 with
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
              let uu____19815 =
                let uu____19818 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____19818
                 in
              FStar_Syntax_Syntax.new_bv uu____19815 t1  in
            let uu____19821 =
              let uu____19826 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____19826
               in
            match uu____19821 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____19882 = FStar_Options.eager_inference ()  in
          if uu____19882
          then
            let uu___196_19883 = probs  in
            {
              attempting = (uu___196_19883.attempting);
              wl_deferred = (uu___196_19883.wl_deferred);
              ctr = (uu___196_19883.ctr);
              defer_ok = false;
              smt_ok = (uu___196_19883.smt_ok);
              tcenv = (uu___196_19883.tcenv);
              wl_implicits = (uu___196_19883.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____19903 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____19903
              then
                let uu____19904 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____19904
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
          ((let uu____19926 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____19926
            then
              let uu____19927 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____19927
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____19931 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____19931
             then
               let uu____19932 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____19932
             else ());
            (let f2 =
               let uu____19935 =
                 let uu____19936 = FStar_Syntax_Util.unmeta f1  in
                 uu____19936.FStar_Syntax_Syntax.n  in
               match uu____19935 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____19940 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___197_19941 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___197_19941.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___197_19941.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___197_19941.FStar_TypeChecker_Env.implicits)
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
            let uu____20055 =
              let uu____20056 =
                let uu____20057 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____20057;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____20056  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____20055
  
let with_guard_no_simp :
  'Auu____20072 .
    'Auu____20072 ->
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
            let uu____20095 =
              let uu____20096 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____20096;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____20095
  
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
          (let uu____20136 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____20136
           then
             let uu____20137 = FStar_Syntax_Print.term_to_string t1  in
             let uu____20138 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____20137
               uu____20138
           else ());
          (let uu____20140 =
             let uu____20145 = empty_worklist env  in
             let uu____20146 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____20145 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____20146
              in
           match uu____20140 with
           | (prob,wl) ->
               let g =
                 let uu____20154 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____20174  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____20154  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____20218 = try_teq true env t1 t2  in
        match uu____20218 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____20222 = FStar_TypeChecker_Env.get_range env  in
              let uu____20223 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____20222 uu____20223);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____20230 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____20230
              then
                let uu____20231 = FStar_Syntax_Print.term_to_string t1  in
                let uu____20232 = FStar_Syntax_Print.term_to_string t2  in
                let uu____20233 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____20231
                  uu____20232 uu____20233
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
          let uu____20255 = FStar_TypeChecker_Env.get_range env  in
          let uu____20256 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____20255 uu____20256
  
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
        (let uu____20281 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____20281
         then
           let uu____20282 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____20283 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____20282 uu____20283
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____20286 =
           let uu____20293 = empty_worklist env  in
           let uu____20294 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____20293 env c1 rel c2 FStar_Pervasives_Native.None
             uu____20294 "sub_comp"
            in
         match uu____20286 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____20304 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____20324  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____20304)
  
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
      fun uu____20379  ->
        match uu____20379 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____20422 =
                 let uu____20427 =
                   let uu____20428 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____20429 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____20428 uu____20429
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____20427)  in
               let uu____20430 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____20422 uu____20430)
               in
            let equiv1 v1 v' =
              let uu____20442 =
                let uu____20447 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____20448 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____20447, uu____20448)  in
              match uu____20442 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____20467 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____20497 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____20497 with
                      | FStar_Syntax_Syntax.U_unif uu____20504 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____20533  ->
                                    match uu____20533 with
                                    | (u,v') ->
                                        let uu____20542 = equiv1 v1 v'  in
                                        if uu____20542
                                        then
                                          let uu____20545 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____20545 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____20561 -> []))
               in
            let uu____20566 =
              let wl =
                let uu___198_20570 = empty_worklist env  in
                {
                  attempting = (uu___198_20570.attempting);
                  wl_deferred = (uu___198_20570.wl_deferred);
                  ctr = (uu___198_20570.ctr);
                  defer_ok = false;
                  smt_ok = (uu___198_20570.smt_ok);
                  tcenv = (uu___198_20570.tcenv);
                  wl_implicits = (uu___198_20570.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____20588  ->
                      match uu____20588 with
                      | (lb,v1) ->
                          let uu____20595 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____20595 with
                           | USolved wl1 -> ()
                           | uu____20597 -> fail1 lb v1)))
               in
            let rec check_ineq uu____20607 =
              match uu____20607 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____20616) -> true
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
                      uu____20639,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____20641,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____20652) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____20659,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____20667 -> false)
               in
            let uu____20672 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____20687  ->
                      match uu____20687 with
                      | (u,v1) ->
                          let uu____20694 = check_ineq (u, v1)  in
                          if uu____20694
                          then true
                          else
                            ((let uu____20697 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____20697
                              then
                                let uu____20698 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____20699 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____20698
                                  uu____20699
                              else ());
                             false)))
               in
            if uu____20672
            then ()
            else
              ((let uu____20703 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____20703
                then
                  ((let uu____20705 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____20705);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____20715 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____20715))
                else ());
               (let uu____20725 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____20725))
  
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
        let fail1 uu____20792 =
          match uu____20792 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___199_20813 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___199_20813.attempting);
            wl_deferred = (uu___199_20813.wl_deferred);
            ctr = (uu___199_20813.ctr);
            defer_ok;
            smt_ok = (uu___199_20813.smt_ok);
            tcenv = (uu___199_20813.tcenv);
            wl_implicits = (uu___199_20813.wl_implicits)
          }  in
        (let uu____20815 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____20815
         then
           let uu____20816 = FStar_Util.string_of_bool defer_ok  in
           let uu____20817 = wl_to_string wl  in
           let uu____20818 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____20816 uu____20817 uu____20818
         else ());
        (let g1 =
           let uu____20831 = solve_and_commit env wl fail1  in
           match uu____20831 with
           | FStar_Pervasives_Native.Some
               (uu____20838::uu____20839,uu____20840) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___200_20865 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___200_20865.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___200_20865.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____20876 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___201_20884 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___201_20884.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___201_20884.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___201_20884.FStar_TypeChecker_Env.implicits)
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
    let uu____20932 = FStar_ST.op_Bang last_proof_ns  in
    match uu____20932 with
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
            let uu___202_21055 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___202_21055.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___202_21055.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___202_21055.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____21056 =
            let uu____21057 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____21057  in
          if uu____21056
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____21065 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____21066 =
                       let uu____21067 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____21067
                        in
                     FStar_Errors.diag uu____21065 uu____21066)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____21071 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____21072 =
                        let uu____21073 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____21073
                         in
                      FStar_Errors.diag uu____21071 uu____21072)
                   else ();
                   (let uu____21076 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____21076 "discharge_guard'"
                      env vc1);
                   (let uu____21077 = check_trivial vc1  in
                    match uu____21077 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____21084 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____21085 =
                                let uu____21086 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____21086
                                 in
                              FStar_Errors.diag uu____21084 uu____21085)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____21091 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____21092 =
                                let uu____21093 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____21093
                                 in
                              FStar_Errors.diag uu____21091 uu____21092)
                           else ();
                           (let vcs =
                              let uu____21106 = FStar_Options.use_tactics ()
                                 in
                              if uu____21106
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____21128  ->
                                     (let uu____21130 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____21130);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____21173  ->
                                              match uu____21173 with
                                              | (env1,goal,opts) ->
                                                  let uu____21189 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____21189, opts)))))
                              else
                                (let uu____21191 =
                                   let uu____21198 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____21198)  in
                                 [uu____21191])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____21235  ->
                                    match uu____21235 with
                                    | (env1,goal,opts) ->
                                        let uu____21251 = check_trivial goal
                                           in
                                        (match uu____21251 with
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
                                                (let uu____21259 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____21260 =
                                                   let uu____21261 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____21262 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____21261 uu____21262
                                                    in
                                                 FStar_Errors.diag
                                                   uu____21259 uu____21260)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____21265 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____21266 =
                                                   let uu____21267 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____21267
                                                    in
                                                 FStar_Errors.diag
                                                   uu____21265 uu____21266)
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
      let uu____21281 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____21281 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____21288 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____21288
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____21299 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____21299 with
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
            let uu____21332 = FStar_Syntax_Util.head_and_args u  in
            match uu____21332 with
            | (hd1,uu____21348) ->
                let uu____21369 =
                  let uu____21370 = FStar_Syntax_Subst.compress u  in
                  uu____21370.FStar_Syntax_Syntax.n  in
                (match uu____21369 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____21373 -> true
                 | uu____21374 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____21394 = acc  in
            match uu____21394 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____21456 = hd1  in
                     (match uu____21456 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____21473 = unresolved tm  in
                             if uu____21473
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___203_21486 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___203_21486.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___203_21486.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___203_21486.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___203_21486.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___203_21486.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___203_21486.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___203_21486.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___203_21486.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___203_21486.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___203_21486.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___203_21486.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___203_21486.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___203_21486.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___203_21486.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___203_21486.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___203_21486.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___203_21486.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___203_21486.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___203_21486.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___203_21486.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___203_21486.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___203_21486.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___203_21486.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___203_21486.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___203_21486.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___203_21486.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___203_21486.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___203_21486.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___203_21486.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___203_21486.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___203_21486.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___203_21486.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___203_21486.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___203_21486.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___203_21486.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___203_21486.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___203_21486.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___204_21489 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___204_21489.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___204_21489.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___204_21489.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___204_21489.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___204_21489.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___204_21489.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___204_21489.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___204_21489.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___204_21489.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___204_21489.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___204_21489.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___204_21489.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___204_21489.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___204_21489.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___204_21489.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___204_21489.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___204_21489.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___204_21489.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___204_21489.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___204_21489.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___204_21489.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___204_21489.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___204_21489.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___204_21489.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___204_21489.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___204_21489.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___204_21489.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___204_21489.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___204_21489.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___204_21489.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___204_21489.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___204_21489.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___204_21489.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___204_21489.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___204_21489.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___204_21489.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___204_21489.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____21492 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "RelCheck")
                                    in
                                 if uu____21492
                                 then
                                   let uu____21493 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____21494 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____21495 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____21496 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____21493 uu____21494 uu____21495
                                     reason uu____21496
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e when FStar_Errors.handleable e ->
                                       ((let uu____21507 =
                                           let uu____21516 =
                                             let uu____21523 =
                                               let uu____21524 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____21525 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____21524 uu____21525
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____21523, r)
                                              in
                                           [uu____21516]  in
                                         FStar_Errors.add_errors uu____21507);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___207_21539 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___207_21539.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___207_21539.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___207_21539.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____21542 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____21549  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____21542 with
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
          let uu___208_21561 = g  in
          let uu____21562 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___208_21561.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___208_21561.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___208_21561.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____21562
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
        let uu____21616 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____21616 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____21627 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____21627
      | (reason,e,ctx_u,r,should_check)::uu____21633 ->
          let uu____21656 =
            let uu____21661 =
              let uu____21662 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____21663 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____21664 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____21662 uu____21663 reason uu____21664
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____21661)
             in
          FStar_Errors.raise_error uu____21656 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___209_21675 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___209_21675.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___209_21675.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___209_21675.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____21690 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____21690 with
      | FStar_Pervasives_Native.Some uu____21696 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21712 = try_teq false env t1 t2  in
        match uu____21712 with
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
        (let uu____21746 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21746
         then
           let uu____21747 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____21748 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____21747
             uu____21748
         else ());
        (let uu____21750 =
           let uu____21757 = empty_worklist env  in
           new_t_prob uu____21757 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____21750 with
         | (prob,x,wl) ->
             let g =
               let uu____21770 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____21790  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____21770  in
             ((let uu____21820 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____21820
               then
                 let uu____21821 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____21822 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____21823 =
                   let uu____21824 = FStar_Util.must g  in
                   guard_to_string env uu____21824  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____21821 uu____21822 uu____21823
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
        let uu____21858 = check_subtyping env t1 t2  in
        match uu____21858 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____21877 =
              let uu____21878 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____21878 g  in
            FStar_Pervasives_Native.Some uu____21877
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21896 = check_subtyping env t1 t2  in
        match uu____21896 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____21915 =
              let uu____21916 =
                let uu____21917 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____21917]  in
              close_guard env uu____21916 g  in
            FStar_Pervasives_Native.Some uu____21915
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____21946 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21946
         then
           let uu____21947 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____21948 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____21947
             uu____21948
         else ());
        (let uu____21950 =
           let uu____21957 = empty_worklist env  in
           new_t_prob uu____21957 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____21950 with
         | (prob,x,wl) ->
             let g =
               let uu____21964 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____21984  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____21964  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____22015 =
                      let uu____22016 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____22016]  in
                    close_guard env uu____22015 g1  in
                  discharge_guard_nosmt env g2))
  