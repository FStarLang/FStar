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
        FStar_TypeChecker_Env.univ_ineqs = ([],[]);
        FStar_TypeChecker_Env.implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun uu____79  ->
                match uu____79 with
                | (uu____88,uu____89,ctx_uvar,uu____91) ->
                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_should_check =
                       FStar_Syntax_Syntax.Allow_unresolved)
                      ||
                      (let uu____94 =
                         FStar_Syntax_Unionfind.find
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       (match uu____94 with
                        | FStar_Pervasives_Native.Some uu____97 -> true
                        | FStar_Pervasives_Native.None  -> false))))
    | uu____98 -> false
  
let (is_trivial_guard_formula : FStar_TypeChecker_Env.guard_t -> Prims.bool)
  =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = uu____104;
        FStar_TypeChecker_Env.univ_ineqs = uu____105;
        FStar_TypeChecker_Env.implicits = uu____106;_} -> true
    | uu____125 -> false
  
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
          let uu___150_160 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___150_160.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___150_160.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___150_160.FStar_TypeChecker_Env.implicits)
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
          let uu____195 = FStar_Options.defensive ()  in
          if uu____195
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____199 =
              let uu____200 =
                let uu____201 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____201  in
              Prims.op_Negation uu____200  in
            (if uu____199
             then
               let uu____206 =
                 let uu____211 =
                   let uu____212 = FStar_Syntax_Print.term_to_string t  in
                   let uu____213 =
                     let uu____214 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____214
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____212 uu____213
                    in
                 (FStar_Errors.Warning_Defensive, uu____211)  in
               FStar_Errors.log_issue rng uu____206
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> unit) =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____236 =
          let uu____237 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____237  in
        if uu____236
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
          let uu____263 =
            let uu____264 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____264  in
          if uu____263
          then ()
          else
            (let uu____266 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____266 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____289 =
            let uu____290 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____290  in
          if uu____289
          then ()
          else
            (let uu____292 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____292 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___151_306 = g  in
          let uu____307 =
            let uu____308 =
              let uu____309 =
                let uu____316 =
                  let uu____317 =
                    let uu____332 =
                      let uu____341 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____341]  in
                    (f, uu____332)  in
                  FStar_Syntax_Syntax.Tm_app uu____317  in
                FStar_Syntax_Syntax.mk uu____316  in
              uu____309 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____308
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____307;
            FStar_TypeChecker_Env.deferred =
              (uu___151_306.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___151_306.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___151_306.FStar_TypeChecker_Env.implicits)
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
          let uu___152_389 = g  in
          let uu____390 =
            let uu____391 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____391  in
          {
            FStar_TypeChecker_Env.guard_f = uu____390;
            FStar_TypeChecker_Env.deferred =
              (uu___152_389.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___152_389.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___152_389.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____397 -> failwith "impossible"
  
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
          let uu____412 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____412
  
let (check_trivial :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Common.guard_formula)
  =
  fun t  ->
    let uu____422 =
      let uu____423 = FStar_Syntax_Util.unmeta t  in
      uu____423.FStar_Syntax_Syntax.n  in
    match uu____422 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____427 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____468 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____468;
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
                       let uu____553 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____553
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___153_555 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___153_555.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___153_555.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___153_555.FStar_TypeChecker_Env.implicits)
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
               let uu____596 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____596
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
            let uu___154_615 = g  in
            let uu____616 =
              let uu____617 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____617  in
            {
              FStar_TypeChecker_Env.guard_f = uu____616;
              FStar_TypeChecker_Env.deferred =
                (uu___154_615.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___154_615.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___154_615.FStar_TypeChecker_Env.implicits)
            }
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____646 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____676 -> false
  
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
              FStar_Syntax_Syntax.should_check_uvar ->
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
                  let uu____963 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____963;
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
                   (let uu___155_997 = wl  in
                    {
                      attempting = (uu___155_997.attempting);
                      wl_deferred = (uu___155_997.wl_deferred);
                      ctr = (uu___155_997.ctr);
                      defer_ok = (uu___155_997.defer_ok);
                      smt_ok = (uu___155_997.smt_ok);
                      tcenv = (uu___155_997.tcenv);
                      wl_implicits = ((reason, t, ctx_uvar, r) ::
                        (wl.wl_implicits))
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
    match projectee with | Success _0 -> true | uu____1059 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1089 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____1114 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1120 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1126 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
[@@deriving show]
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
[@@deriving show]
type 'a problem_t = 'a FStar_TypeChecker_Common.problem[@@deriving show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___118_1141  ->
    match uu___118_1141 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1147 = FStar_Syntax_Util.head_and_args t  in
    match uu____1147 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1206 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1207 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1221 =
                     let uu____1222 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1222  in
                   FStar_Util.format1 "@<%s>" uu____1221
                in
             let uu____1225 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1206 uu____1207 uu____1225
         | uu____1226 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___119_1236  ->
      match uu___119_1236 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1240 =
            let uu____1243 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1244 =
              let uu____1247 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1248 =
                let uu____1251 =
                  let uu____1254 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1254]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1251
                 in
              uu____1247 :: uu____1248  in
            uu____1243 :: uu____1244  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1240
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1258 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1259 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1260 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1258 uu____1259
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1260
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___120_1270  ->
      match uu___120_1270 with
      | UNIV (u,t) ->
          let x =
            let uu____1274 = FStar_Options.hide_uvar_nums ()  in
            if uu____1274
            then "?"
            else
              (let uu____1276 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1276 FStar_Util.string_of_int)
             in
          let uu____1277 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1277
      | TERM (u,t) ->
          let x =
            let uu____1281 = FStar_Options.hide_uvar_nums ()  in
            if uu____1281
            then "?"
            else
              (let uu____1283 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1283 FStar_Util.string_of_int)
             in
          let uu____1284 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1284
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1299 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1299 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1313 =
      let uu____1316 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1316
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1313 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1329 .
    (FStar_Syntax_Syntax.term,'Auu____1329) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1347 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1365  ->
              match uu____1365 with
              | (x,uu____1371) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1347 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1379 =
      let uu____1380 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1380  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1379;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___156_1410 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___156_1410.wl_deferred);
          ctr = (uu___156_1410.ctr);
          defer_ok = (uu___156_1410.defer_ok);
          smt_ok;
          tcenv = (uu___156_1410.tcenv);
          wl_implicits = (uu___156_1410.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1417 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1417,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___157_1440 = empty_worklist env  in
      let uu____1441 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1441;
        wl_deferred = (uu___157_1440.wl_deferred);
        ctr = (uu___157_1440.ctr);
        defer_ok = (uu___157_1440.defer_ok);
        smt_ok = (uu___157_1440.smt_ok);
        tcenv = (uu___157_1440.tcenv);
        wl_implicits = (uu___157_1440.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___158_1461 = wl  in
        {
          attempting = (uu___158_1461.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___158_1461.ctr);
          defer_ok = (uu___158_1461.defer_ok);
          smt_ok = (uu___158_1461.smt_ok);
          tcenv = (uu___158_1461.tcenv);
          wl_implicits = (uu___158_1461.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___159_1482 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___159_1482.wl_deferred);
        ctr = (uu___159_1482.ctr);
        defer_ok = (uu___159_1482.defer_ok);
        smt_ok = (uu___159_1482.smt_ok);
        tcenv = (uu___159_1482.tcenv);
        wl_implicits = (uu___159_1482.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1499 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1499
         then
           let uu____1500 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1500
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___121_1506  ->
    match uu___121_1506 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1511 .
    'Auu____1511 FStar_TypeChecker_Common.problem ->
      'Auu____1511 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___160_1523 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___160_1523.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___160_1523.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___160_1523.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___160_1523.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___160_1523.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___160_1523.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___160_1523.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1530 .
    'Auu____1530 FStar_TypeChecker_Common.problem ->
      'Auu____1530 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___122_1547  ->
    match uu___122_1547 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___123_1562  ->
    match uu___123_1562 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___161_1568 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___161_1568.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___161_1568.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___161_1568.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___161_1568.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___161_1568.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___161_1568.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___161_1568.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___161_1568.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___161_1568.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___162_1576 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___162_1576.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___162_1576.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___162_1576.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___162_1576.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___162_1576.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___162_1576.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___162_1576.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___162_1576.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___162_1576.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___124_1588  ->
      match uu___124_1588 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___125_1593  ->
    match uu___125_1593 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___126_1604  ->
    match uu___126_1604 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___127_1617  ->
    match uu___127_1617 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___128_1630  ->
    match uu___128_1630 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___129_1641  ->
    match uu___129_1641 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___130_1656  ->
    match uu___130_1656 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1675 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1675) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1703 =
          let uu____1704 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1704  in
        if uu____1703
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1738)::bs ->
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
        let uu____1805 =
          let uu____1806 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1806  in
        if uu____1805
        then ()
        else
          (let uu____1808 =
             let uu____1811 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1811
              in
           def_check_closed_in (p_loc prob) msg uu____1808 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1841 =
         let uu____1842 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1842  in
       if uu____1841
       then ()
       else
         (let uu____1844 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1844));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1856 -> ())
  
let mk_eq2 :
  'Auu____1868 .
    worklist ->
      'Auu____1868 ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun _prob  ->
      fun t1  ->
        fun t2  ->
          let env =
            let uu___163_1894 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___163_1894.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___163_1894.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___163_1894.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___163_1894.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___163_1894.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___163_1894.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___163_1894.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___163_1894.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___163_1894.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___163_1894.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___163_1894.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___163_1894.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___163_1894.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___163_1894.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___163_1894.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___163_1894.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___163_1894.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___163_1894.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___163_1894.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___163_1894.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___163_1894.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___163_1894.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___163_1894.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___163_1894.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___163_1894.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___163_1894.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___163_1894.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___163_1894.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___163_1894.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___163_1894.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___163_1894.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___163_1894.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___163_1894.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___163_1894.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___163_1894.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___163_1894.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___163_1894.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____1895 = env.FStar_TypeChecker_Env.type_of env t1  in
          match uu____1895 with
          | (uu____1906,tt,g) ->
              let u = (wl.tcenv).FStar_TypeChecker_Env.universe_of env tt  in
              let uu____1910 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
              (uu____1910,
                (let uu___164_1912 = wl  in
                 {
                   attempting = (uu___164_1912.attempting);
                   wl_deferred = (uu___164_1912.wl_deferred);
                   ctr = (uu___164_1912.ctr);
                   defer_ok = (uu___164_1912.defer_ok);
                   smt_ok = (uu___164_1912.smt_ok);
                   tcenv = (uu___164_1912.tcenv);
                   wl_implicits =
                     (FStar_List.append g.FStar_TypeChecker_Env.implicits
                        wl.wl_implicits)
                 }))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___131_1925  ->
    match uu___131_1925 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1941 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1941 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1953  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2051 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2051 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2051 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2051 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2117 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2117  in
                  let uu____2120 =
                    let uu____2127 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2127
                      guard_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2120 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2148 ->
                            let uu____2155 =
                              let uu____2160 =
                                FStar_List.map
                                  (fun uu____2173  ->
                                     match uu____2173 with
                                     | (x,i) ->
                                         let uu____2184 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2184, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2160  in
                            uu____2155 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2187 =
                        let uu____2190 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2190;
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
                      (uu____2187, wl1)
  
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
                  let uu____2253 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2253 with
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
                  let uu____2330 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2330 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2365 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2365 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2365 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2365 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2416 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2471 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2471]  in
                        let uu____2484 =
                          let uu____2487 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2487  in
                        let uu____2490 =
                          let uu____2493 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2493  in
                        (bs, uu____2484, uu____2490)
                     in
                  match uu____2416 with
                  | (bs,lg_ty,elt) ->
                      let uu____2533 =
                        let uu____2540 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___165_2548 = wl  in
                           {
                             attempting = (uu___165_2548.attempting);
                             wl_deferred = (uu___165_2548.wl_deferred);
                             ctr = (uu___165_2548.ctr);
                             defer_ok = (uu___165_2548.defer_ok);
                             smt_ok = (uu___165_2548.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___165_2548.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2540
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2533 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2560 =
                                   let uu____2565 =
                                     let uu____2566 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2566]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2565
                                    in
                                 uu____2560 FStar_Pervasives_Native.None loc
                              in
                           let uu____2587 =
                             let uu____2590 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2590;
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
                           (uu____2587, wl1))
  
let problem_using_guard :
  'Auu____2607 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2607 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2607 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2607 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2644 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2644;
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
  'Auu____2655 .
    worklist ->
      'Auu____2655 FStar_TypeChecker_Common.problem ->
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
        let uu____2705 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2705
        then
          let uu____2706 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2707 = prob_to_string env d  in
          let uu____2708 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2706 uu____2707 uu____2708 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2714 -> failwith "impossible"  in
           let uu____2715 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2727 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2728 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2727, uu____2728)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2732 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2733 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2732, uu____2733)
              in
           match uu____2715 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___132_2751  ->
            match uu___132_2751 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2763 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___133_2785  ->
           match uu___133_2785 with
           | UNIV uu____2788 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2795 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2795
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
        (fun uu___134_2819  ->
           match uu___134_2819 with
           | UNIV (u',t) ->
               let uu____2824 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2824
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2828 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2839 =
        let uu____2840 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2840
         in
      FStar_Syntax_Subst.compress uu____2839
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2851 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2851
  
let norm_arg :
  'Auu____2858 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2858) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2858)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2881 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2881, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2922  ->
              match uu____2922 with
              | (x,imp) ->
                  let uu____2933 =
                    let uu___166_2934 = x  in
                    let uu____2935 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___166_2934.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___166_2934.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2935
                    }  in
                  (uu____2933, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2956 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2956
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2960 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2960
        | uu____2963 -> u2  in
      let uu____2964 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2964
  
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
                (let uu____3078 = norm_refinement env t12  in
                 match uu____3078 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3093;
                     FStar_Syntax_Syntax.vars = uu____3094;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3120 =
                       let uu____3121 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3122 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3121 uu____3122
                        in
                     failwith uu____3120)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3136 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3136
          | FStar_Syntax_Syntax.Tm_uinst uu____3137 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3172 =
                   let uu____3173 = FStar_Syntax_Subst.compress t1'  in
                   uu____3173.FStar_Syntax_Syntax.n  in
                 match uu____3172 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3188 -> aux true t1'
                 | uu____3195 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3210 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3239 =
                   let uu____3240 = FStar_Syntax_Subst.compress t1'  in
                   uu____3240.FStar_Syntax_Syntax.n  in
                 match uu____3239 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3255 -> aux true t1'
                 | uu____3262 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3277 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3320 =
                   let uu____3321 = FStar_Syntax_Subst.compress t1'  in
                   uu____3321.FStar_Syntax_Syntax.n  in
                 match uu____3320 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3336 -> aux true t1'
                 | uu____3343 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3358 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3373 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3388 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3403 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3418 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3445 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3476 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3497 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3526 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3553 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3590 ->
              let uu____3597 =
                let uu____3598 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3599 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3598 uu____3599
                 in
              failwith uu____3597
          | FStar_Syntax_Syntax.Tm_ascribed uu____3612 ->
              let uu____3639 =
                let uu____3640 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3641 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3640 uu____3641
                 in
              failwith uu____3639
          | FStar_Syntax_Syntax.Tm_delayed uu____3654 ->
              let uu____3679 =
                let uu____3680 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3681 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3680 uu____3681
                 in
              failwith uu____3679
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3694 =
                let uu____3695 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3696 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3695 uu____3696
                 in
              failwith uu____3694
           in
        let uu____3709 = whnf env t1  in aux false uu____3709
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3740 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3740 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3771 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3771 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3807 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3807, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3818 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3818 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3843 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3843 with
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
  fun uu____3920  ->
    match uu____3920 with
    | (t_base,refopt) ->
        let uu____3953 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3953 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3993 =
      let uu____3996 =
        let uu____3999 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4022  ->
                  match uu____4022 with | (uu____4029,uu____4030,x) -> x))
           in
        FStar_List.append wl.attempting uu____3999  in
      FStar_List.map (wl_prob_to_string wl) uu____3996  in
    FStar_All.pipe_right uu____3993 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____4044 .
    ('Auu____4044,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4055  ->
    match uu____4055 with
    | (uu____4062,c,args) ->
        let uu____4065 = print_ctx_uvar c  in
        let uu____4066 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4065 uu____4066
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4072 = FStar_Syntax_Util.head_and_args t  in
    match uu____4072 with
    | (head1,_args) ->
        let uu____4109 =
          let uu____4110 = FStar_Syntax_Subst.compress head1  in
          uu____4110.FStar_Syntax_Syntax.n  in
        (match uu____4109 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4113 -> true
         | uu____4128 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4134 = FStar_Syntax_Util.head_and_args t  in
    match uu____4134 with
    | (head1,_args) ->
        let uu____4171 =
          let uu____4172 = FStar_Syntax_Subst.compress head1  in
          uu____4172.FStar_Syntax_Syntax.n  in
        (match uu____4171 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4176) -> u
         | uu____4197 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4220 = FStar_Syntax_Util.head_and_args t  in
      match uu____4220 with
      | (head1,args) ->
          let uu____4261 =
            let uu____4262 = FStar_Syntax_Subst.compress head1  in
            uu____4262.FStar_Syntax_Syntax.n  in
          (match uu____4261 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4270)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4313 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___135_4338  ->
                         match uu___135_4338 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4342 =
                               let uu____4343 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4343.FStar_Syntax_Syntax.n  in
                             (match uu____4342 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4347 -> false)
                         | uu____4348 -> true))
                  in
               (match uu____4313 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4370 =
                        FStar_List.collect
                          (fun uu___136_4376  ->
                             match uu___136_4376 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4380 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4380]
                             | uu____4381 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4370 FStar_List.rev  in
                    let uu____4390 =
                      let uu____4397 =
                        let uu____4404 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___137_4418  ->
                                  match uu___137_4418 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4422 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4422]
                                  | uu____4423 -> []))
                           in
                        FStar_All.pipe_right uu____4404 FStar_List.rev  in
                      let uu____4440 =
                        let uu____4443 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4443  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4397 uu____4440
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4390 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4472  ->
                                match uu____4472 with
                                | (x,i) ->
                                    let uu____4483 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4483, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4506  ->
                                match uu____4506 with
                                | (a,i) ->
                                    let uu____4517 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4517, i)) args_sol
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
           | uu____4533 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4553 =
          let uu____4566 =
            let uu____4567 = FStar_Syntax_Subst.compress k  in
            uu____4567.FStar_Syntax_Syntax.n  in
          match uu____4566 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4620 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4620)
              else
                (let uu____4634 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4634 with
                 | (ys',t1,uu____4657) ->
                     let uu____4662 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4662))
          | uu____4703 ->
              let uu____4704 =
                let uu____4715 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4715)  in
              ((ys, t), uu____4704)
           in
        match uu____4553 with
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
                 let uu____4764 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4764 c  in
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
               (let uu____4838 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4838
                then
                  let uu____4839 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4840 = print_ctx_uvar uv  in
                  let uu____4841 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4839 uu____4840 uu____4841
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
             let uu____4847 = p_guard_uvar prob  in
             match uu____4847 with
             | (xs,uv) ->
                 let fail1 uu____4859 =
                   let uu____4860 =
                     let uu____4861 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4862 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4861 uu____4862
                      in
                   failwith uu____4860  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____4912  ->
                           match uu____4912 with
                           | (a,i) ->
                               let uu____4925 =
                                 let uu____4926 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____4926.FStar_Syntax_Syntax.n  in
                               (match uu____4925 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____4944 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____4952 =
                     let uu____4953 = is_flex g  in
                     Prims.op_Negation uu____4953  in
                   if uu____4952
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____4957 = destruct_flex_t g wl  in
                      match uu____4957 with
                      | ((uu____4962,uv1,args),wl1) ->
                          ((let uu____4967 = args_as_binders args  in
                            assign_solution uu____4967 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___167_4969 = wl1  in
                   {
                     attempting = (uu___167_4969.attempting);
                     wl_deferred = (uu___167_4969.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___167_4969.defer_ok);
                     smt_ok = (uu___167_4969.smt_ok);
                     tcenv = (uu___167_4969.tcenv);
                     wl_implicits = (uu___167_4969.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4990 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4990
         then
           let uu____4991 = FStar_Util.string_of_int pid  in
           let uu____4992 =
             let uu____4993 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4993 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4991 uu____4992
         else ());
        commit sol;
        (let uu___168_5000 = wl  in
         {
           attempting = (uu___168_5000.attempting);
           wl_deferred = (uu___168_5000.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___168_5000.defer_ok);
           smt_ok = (uu___168_5000.smt_ok);
           tcenv = (uu___168_5000.tcenv);
           wl_implicits = (uu___168_5000.wl_implicits)
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
             | (uu____5062,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5088 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5088
              in
           (let uu____5094 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5094
            then
              let uu____5095 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5096 =
                let uu____5097 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5097 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5095 uu____5096
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
        let uu____5122 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5122 FStar_Util.set_elements  in
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
      let uu____5156 = occurs uk t  in
      match uu____5156 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5185 =
                 let uu____5186 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5187 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5186 uu____5187
                  in
               FStar_Pervasives_Native.Some uu____5185)
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
            let uu____5276 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5276 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5320 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5368  ->
             match uu____5368 with
             | (x,uu____5378) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5391 = FStar_List.last bs  in
      match uu____5391 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5409) ->
          let uu____5414 =
            FStar_Util.prefix_until
              (fun uu___138_5429  ->
                 match uu___138_5429 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5431 -> false) g
             in
          (match uu____5414 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5444,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5480 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5480 with
        | (pfx,uu____5490) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5502 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5502 with
             | (uu____5509,src',wl1) ->
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
                 | uu____5609 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5610 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5664  ->
                  fun uu____5665  ->
                    match (uu____5664, uu____5665) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5746 =
                          let uu____5747 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5747
                           in
                        if uu____5746
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5772 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5772
                           then
                             let uu____5785 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5785)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5610 with | (isect,uu____5822) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5851 'Auu____5852 .
    (FStar_Syntax_Syntax.bv,'Auu____5851) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5852) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5909  ->
              fun uu____5910  ->
                match (uu____5909, uu____5910) with
                | ((a,uu____5928),(b,uu____5930)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5945 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5945) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5975  ->
           match uu____5975 with
           | (y,uu____5981) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5992 'Auu____5993 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5992) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5993)
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
                   let uu____6102 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6102
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____6110 =
                        let uu____6113 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____6113 :: seen  in
                      aux uu____6110 args2)
               | uu____6114 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6144 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____6181 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6187 -> false
  
let string_of_option :
  'Auu____6194 .
    ('Auu____6194 -> Prims.string) ->
      'Auu____6194 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___139_6209  ->
      match uu___139_6209 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6215 = f x  in Prims.strcat "Some " uu____6215
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___140_6220  ->
    match uu___140_6220 with
    | MisMatch (d1,d2) ->
        let uu____6231 =
          let uu____6232 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6233 =
            let uu____6234 =
              let uu____6235 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6235 ")"  in
            Prims.strcat ") (" uu____6234  in
          Prims.strcat uu____6232 uu____6233  in
        Prims.strcat "MisMatch (" uu____6231
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___141_6240  ->
    match uu___141_6240 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____6255 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____6285 = m2 ()  in
          (match uu____6285 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____6300 -> HeadMatch)
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
          let uu____6314 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6314 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6325 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6348 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6357 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6385 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6385
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6386 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6387 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6388 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6403 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6416 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6440) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6446,uu____6447) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6489) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6510;
             FStar_Syntax_Syntax.index = uu____6511;
             FStar_Syntax_Syntax.sort = t2;_},uu____6513)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6520 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6521 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6522 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6535 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6542 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6560 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6560
  
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
            let uu____6587 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6587
            then FullMatch
            else
              (let uu____6589 =
                 let uu____6598 =
                   let uu____6601 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6601  in
                 let uu____6602 =
                   let uu____6605 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6605  in
                 (uu____6598, uu____6602)  in
               MisMatch uu____6589)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6611),FStar_Syntax_Syntax.Tm_uinst (g,uu____6613)) ->
            let uu____6622 = head_matches env f g  in
            FStar_All.pipe_right uu____6622 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6625 = FStar_Const.eq_const c d  in
            if uu____6625
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6632),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6634)) ->
            let uu____6675 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6675
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6682),FStar_Syntax_Syntax.Tm_refine (y,uu____6684)) ->
            let uu____6693 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6693 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6695),uu____6696) ->
            let uu____6701 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6701 head_match
        | (uu____6702,FStar_Syntax_Syntax.Tm_refine (x,uu____6704)) ->
            let uu____6709 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6709 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6710,FStar_Syntax_Syntax.Tm_type
           uu____6711) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6712,FStar_Syntax_Syntax.Tm_arrow uu____6713) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6739),FStar_Syntax_Syntax.Tm_app (head',uu____6741))
            ->
            let uu____6782 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6782 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6784),uu____6785) ->
            let uu____6806 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6806 head_match
        | (uu____6807,FStar_Syntax_Syntax.Tm_app (head1,uu____6809)) ->
            let uu____6830 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6830 head_match
        | uu____6831 ->
            let uu____6836 =
              let uu____6845 = delta_depth_of_term env t11  in
              let uu____6848 = delta_depth_of_term env t21  in
              (uu____6845, uu____6848)  in
            MisMatch uu____6836
  
let head_matches_delta :
  'Auu____6865 .
    FStar_TypeChecker_Env.env ->
      'Auu____6865 ->
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
            let uu____6912 = FStar_Syntax_Util.head_and_args t  in
            match uu____6912 with
            | (head1,uu____6930) ->
                let uu____6951 =
                  let uu____6952 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6952.FStar_Syntax_Syntax.n  in
                (match uu____6951 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6958 =
                       let uu____6959 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6959 FStar_Option.isSome
                        in
                     if uu____6958
                     then
                       let uu____6978 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6978
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6982 -> FStar_Pervasives_Native.None)
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
              let uu____7115 =
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
              match uu____7115 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____7160 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____7160 with
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
                 uu____7192),uu____7193)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7211 =
                     let uu____7220 = maybe_inline t11  in
                     let uu____7223 = maybe_inline t21  in
                     (uu____7220, uu____7223)  in
                   match uu____7211 with
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
                (uu____7260,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____7261))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7279 =
                     let uu____7288 = maybe_inline t11  in
                     let uu____7291 = maybe_inline t21  in
                     (uu____7288, uu____7291)  in
                   match uu____7279 with
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
            | MisMatch uu____7340 -> fail1 r
            | uu____7349 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7362 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7362
           then
             let uu____7363 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7364 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7365 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7372 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7390 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7390
                    (fun uu____7424  ->
                       match uu____7424 with
                       | (t11,t21) ->
                           let uu____7431 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7432 =
                             let uu____7433 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7433  in
                           Prims.strcat uu____7431 uu____7432))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____7363
               uu____7364 uu____7365 uu____7372
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7445 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7445 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___142_7458  ->
    match uu___142_7458 with
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
      let uu___169_7495 = p  in
      let uu____7498 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7499 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___169_7495.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7498;
        FStar_TypeChecker_Common.relation =
          (uu___169_7495.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7499;
        FStar_TypeChecker_Common.element =
          (uu___169_7495.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___169_7495.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___169_7495.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___169_7495.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___169_7495.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___169_7495.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7513 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7513
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____7518 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7540 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7540 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7548 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7548 with
           | (lh,lhs_args) ->
               let uu____7589 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7589 with
                | (rh,rhs_args) ->
                    let uu____7630 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7643,FStar_Syntax_Syntax.Tm_uvar uu____7644)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7725 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7748,uu____7749)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___170_7767 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_7767.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_7767.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_7767.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_7767.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_7767.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___170_7767.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_7767.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_7767.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_7767.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7770,FStar_Syntax_Syntax.Tm_uvar uu____7771)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___170_7789 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_7789.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_7789.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_7789.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_7789.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_7789.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___170_7789.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_7789.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_7789.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_7789.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7792,FStar_Syntax_Syntax.Tm_arrow uu____7793)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___171_7823 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_7823.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___171_7823.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_7823.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_7823.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_7823.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___171_7823.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_7823.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_7823.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_7823.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7826,FStar_Syntax_Syntax.Tm_type uu____7827)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___171_7845 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_7845.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___171_7845.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_7845.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_7845.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_7845.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___171_7845.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_7845.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_7845.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_7845.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7848,FStar_Syntax_Syntax.Tm_uvar uu____7849)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___171_7867 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_7867.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___171_7867.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_7867.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_7867.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_7867.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___171_7867.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_7867.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_7867.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_7867.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7870,FStar_Syntax_Syntax.Tm_uvar uu____7871)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7888,uu____7889)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7906,FStar_Syntax_Syntax.Tm_uvar uu____7907)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7924,uu____7925) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7630 with
                     | (rank,tp1) ->
                         let uu____7938 =
                           FStar_All.pipe_right
                             (let uu___172_7942 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___172_7942.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___172_7942.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___172_7942.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___172_7942.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___172_7942.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___172_7942.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___172_7942.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___172_7942.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___172_7942.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7938))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7948 =
            FStar_All.pipe_right
              (let uu___173_7952 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___173_7952.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___173_7952.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___173_7952.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___173_7952.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___173_7952.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___173_7952.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___173_7952.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___173_7952.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___173_7952.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7948)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8013 probs =
      match uu____8013 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8094 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8115 = rank wl.tcenv hd1  in
               (match uu____8115 with
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
                      (let uu____8174 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8178 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8178)
                          in
                       if uu____8174
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
          let uu____8246 = FStar_Syntax_Util.head_and_args t  in
          match uu____8246 with
          | (hd1,uu____8262) ->
              let uu____8283 =
                let uu____8284 = FStar_Syntax_Subst.compress hd1  in
                uu____8284.FStar_Syntax_Syntax.n  in
              (match uu____8283 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8288) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8322  ->
                           match uu____8322 with
                           | (y,uu____8328) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8342  ->
                                       match uu____8342 with
                                       | (x,uu____8348) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8349 -> false)
           in
        let uu____8350 = rank tcenv p  in
        match uu____8350 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8357 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8384 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8398 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8412 -> false
  
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
                        let uu____8464 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8464 with
                        | (k,uu____8470) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8480 -> false)))
            | uu____8481 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8533 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8539 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8539 = (Prims.parse_int "0")))
                           in
                        if uu____8533 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8555 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8561 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8561 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8555)
               in
            let uu____8562 = filter1 u12  in
            let uu____8565 = filter1 u22  in (uu____8562, uu____8565)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8594 = filter_out_common_univs us1 us2  in
                (match uu____8594 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8653 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8653 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8656 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8666 =
                          let uu____8667 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8668 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8667
                            uu____8668
                           in
                        UFailed uu____8666))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8692 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8692 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8718 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8718 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8721 ->
                let uu____8726 =
                  let uu____8727 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8728 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8727
                    uu____8728 msg
                   in
                UFailed uu____8726
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8729,uu____8730) ->
              let uu____8731 =
                let uu____8732 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8733 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8732 uu____8733
                 in
              failwith uu____8731
          | (FStar_Syntax_Syntax.U_unknown ,uu____8734) ->
              let uu____8735 =
                let uu____8736 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8737 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8736 uu____8737
                 in
              failwith uu____8735
          | (uu____8738,FStar_Syntax_Syntax.U_bvar uu____8739) ->
              let uu____8740 =
                let uu____8741 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8742 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8741 uu____8742
                 in
              failwith uu____8740
          | (uu____8743,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8744 =
                let uu____8745 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8746 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8745 uu____8746
                 in
              failwith uu____8744
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8770 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8770
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8784 = occurs_univ v1 u3  in
              if uu____8784
              then
                let uu____8785 =
                  let uu____8786 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8787 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8786 uu____8787
                   in
                try_umax_components u11 u21 uu____8785
              else
                (let uu____8789 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8789)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8801 = occurs_univ v1 u3  in
              if uu____8801
              then
                let uu____8802 =
                  let uu____8803 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8804 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8803 uu____8804
                   in
                try_umax_components u11 u21 uu____8802
              else
                (let uu____8806 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8806)
          | (FStar_Syntax_Syntax.U_max uu____8807,uu____8808) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8814 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8814
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8816,FStar_Syntax_Syntax.U_max uu____8817) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8823 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8823
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8825,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8826,FStar_Syntax_Syntax.U_name
             uu____8827) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8828) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8829) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8830,FStar_Syntax_Syntax.U_succ
             uu____8831) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8832,FStar_Syntax_Syntax.U_zero
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
      let uu____8932 = bc1  in
      match uu____8932 with
      | (bs1,mk_cod1) ->
          let uu____8976 = bc2  in
          (match uu____8976 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9087 = aux xs ys  in
                     (match uu____9087 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9170 =
                       let uu____9177 = mk_cod1 xs  in ([], uu____9177)  in
                     let uu____9180 =
                       let uu____9187 = mk_cod2 ys  in ([], uu____9187)  in
                     (uu____9170, uu____9180)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____9210 'Auu____9211 'Auu____9212 .
    ('Auu____9210,'Auu____9211,'Auu____9212 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___143_9225  ->
    match uu___143_9225 with
    | (uu____9234,uu____9235,[]) -> true
    | uu____9238 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9269 = f  in
      match uu____9269 with
      | (uu____9276,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9277;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9278;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9281;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9282;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9283;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9335  ->
                 match uu____9335 with
                 | (y,uu____9341) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9463 =
                  let uu____9476 =
                    let uu____9479 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9479  in
                  ((FStar_List.rev pat_binders), uu____9476)  in
                FStar_Pervasives_Native.Some uu____9463
            | (uu____9506,[]) ->
                let uu____9529 =
                  let uu____9542 =
                    let uu____9545 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9545  in
                  ((FStar_List.rev pat_binders), uu____9542)  in
                FStar_Pervasives_Native.Some uu____9529
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9610 =
                  let uu____9611 = FStar_Syntax_Subst.compress a  in
                  uu____9611.FStar_Syntax_Syntax.n  in
                (match uu____9610 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9629 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9629
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___174_9650 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___174_9650.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___174_9650.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9654 =
                            let uu____9655 =
                              let uu____9662 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9662)  in
                            FStar_Syntax_Syntax.NT uu____9655  in
                          [uu____9654]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___175_9674 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___175_9674.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___175_9674.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9675 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9703 =
                  let uu____9716 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9716  in
                (match uu____9703 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9779 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9806 ->
               let uu____9807 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9807 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10083 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10083
       then
         let uu____10084 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10084
       else ());
      (let uu____10086 = next_prob probs  in
       match uu____10086 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___176_10113 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___176_10113.wl_deferred);
               ctr = (uu___176_10113.ctr);
               defer_ok = (uu___176_10113.defer_ok);
               smt_ok = (uu___176_10113.smt_ok);
               tcenv = (uu___176_10113.tcenv);
               wl_implicits = (uu___176_10113.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10120 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10120
                then
                  let uu____10121 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10121
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
                          (let uu___177_10126 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___177_10126.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___177_10126.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___177_10126.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___177_10126.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___177_10126.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___177_10126.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___177_10126.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___177_10126.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___177_10126.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10148 ->
                let uu____10157 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10216  ->
                          match uu____10216 with
                          | (c,uu____10224,uu____10225) -> c < probs.ctr))
                   in
                (match uu____10157 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10266 =
                            let uu____10271 =
                              FStar_List.map
                                (fun uu____10286  ->
                                   match uu____10286 with
                                   | (uu____10297,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10271, (probs.wl_implicits))  in
                          Success uu____10266
                      | uu____10300 ->
                          let uu____10309 =
                            let uu___178_10310 = probs  in
                            let uu____10311 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10330  ->
                                      match uu____10330 with
                                      | (uu____10337,uu____10338,y) -> y))
                               in
                            {
                              attempting = uu____10311;
                              wl_deferred = rest;
                              ctr = (uu___178_10310.ctr);
                              defer_ok = (uu___178_10310.defer_ok);
                              smt_ok = (uu___178_10310.smt_ok);
                              tcenv = (uu___178_10310.tcenv);
                              wl_implicits = (uu___178_10310.wl_implicits)
                            }  in
                          solve env uu____10309))))

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
            let uu____10345 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10345 with
            | USolved wl1 ->
                let uu____10347 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10347
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
                  let uu____10399 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10399 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10402 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10414;
                  FStar_Syntax_Syntax.vars = uu____10415;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10418;
                  FStar_Syntax_Syntax.vars = uu____10419;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10431,uu____10432) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10439,FStar_Syntax_Syntax.Tm_uinst uu____10440) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10447 -> USolved wl

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
            ((let uu____10457 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10457
              then
                let uu____10458 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10458 msg
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
              let uu____10543 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10543 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10595 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10595
               then
                 let uu____10596 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10597 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10596
                   uu____10597
               else ());
              (let uu____10599 = head_matches_delta env1 () t1 t2  in
               match uu____10599 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____10644 ->
                        let uu____10653 = eq_prob t1 t2 wl2  in
                        (match uu____10653 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____10700 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10715 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10716 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10715, uu____10716)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10721 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10722 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10721, uu____10722)
                           in
                        (match uu____10700 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10753 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10753 with
                               | (t1_hd,t1_args) ->
                                   let uu____10792 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10792 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____10846 =
                                             let uu____10853 =
                                               let uu____10862 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____10862 :: t1_args  in
                                             let uu____10875 =
                                               let uu____10882 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____10882 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____10923  ->
                                                  fun uu____10924  ->
                                                    fun uu____10925  ->
                                                      match (uu____10923,
                                                              uu____10924,
                                                              uu____10925)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____10967),
                                                         (a2,uu____10969)) ->
                                                          let uu____10994 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____10994
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____10853
                                               uu____10875
                                              in
                                           match uu____10846 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___179_11020 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___179_11020.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___179_11020.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11036 =
                                                 solve env1 wl'  in
                                               (match uu____11036 with
                                                | Success (uu____11039,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___180_11043 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___180_11043.attempting);
                                                           wl_deferred =
                                                             (uu___180_11043.wl_deferred);
                                                           ctr =
                                                             (uu___180_11043.ctr);
                                                           defer_ok =
                                                             (uu___180_11043.defer_ok);
                                                           smt_ok =
                                                             (uu___180_11043.smt_ok);
                                                           tcenv =
                                                             (uu___180_11043.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11052 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11084 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11084 with
                               | (t1_base,p1_opt) ->
                                   let uu____11125 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11125 with
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
                                              let uu____11256 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____11256
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
                                              let uu____11286 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11286
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
                                              let uu____11316 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11316
                                          | uu____11319 -> t_base  in
                                        let uu____11336 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11336 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11350 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11350, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11357 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11357 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11398 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11398 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11439 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11439
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
                             let uu____11463 = combine t11 t21 wl2  in
                             (match uu____11463 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11496 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11496
                                    then
                                      let uu____11497 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11497
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11536 ts1 =
              match uu____11536 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11599 = pairwise out t wl2  in
                       (match uu____11599 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11635 =
              let uu____11646 = FStar_List.hd ts  in (uu____11646, [], wl1)
               in
            let uu____11655 = FStar_List.tl ts  in
            aux uu____11635 uu____11655  in
          let uu____11662 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11662 with
          | (this_flex,this_rigid) ->
              let uu____11674 =
                let uu____11675 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11675.FStar_Syntax_Syntax.n  in
              (match uu____11674 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11696 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11696
                   then
                     let uu____11697 = destruct_flex_t this_flex wl  in
                     (match uu____11697 with
                      | (flex,wl1) ->
                          let uu____11704 = quasi_pattern env flex  in
                          (match uu____11704 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11722 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11722
                                 then
                                   let uu____11723 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11723
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
                             ((let uu___181_11728 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___181_11728.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___181_11728.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___181_11728.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___181_11728.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___181_11728.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___181_11728.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___181_11728.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___181_11728.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___181_11728.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11729 ->
                   ((let uu____11731 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11731
                     then
                       let uu____11732 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11732
                     else ());
                    (let uu____11734 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11734 with
                     | (u,_args) ->
                         let uu____11771 =
                           let uu____11772 = FStar_Syntax_Subst.compress u
                              in
                           uu____11772.FStar_Syntax_Syntax.n  in
                         (match uu____11771 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____11803 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____11803 with
                                | (u',uu____11819) ->
                                    let uu____11840 =
                                      let uu____11841 = whnf env u'  in
                                      uu____11841.FStar_Syntax_Syntax.n  in
                                    (match uu____11840 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____11866 -> false)
                                 in
                              let uu____11867 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___144_11890  ->
                                        match uu___144_11890 with
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
                                             | uu____11899 -> false)
                                        | uu____11902 -> false))
                                 in
                              (match uu____11867 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____11916 = whnf env this_rigid
                                        in
                                     let uu____11917 =
                                       FStar_List.collect
                                         (fun uu___145_11923  ->
                                            match uu___145_11923 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____11929 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____11929]
                                            | uu____11931 -> []) bounds_probs
                                        in
                                     uu____11916 :: uu____11917  in
                                   let uu____11932 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____11932 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____11963 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____11978 =
                                              let uu____11979 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____11979.FStar_Syntax_Syntax.n
                                               in
                                            match uu____11978 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____11991 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____11991)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____12000 -> bound  in
                                          let uu____12001 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____12001)  in
                                        (match uu____11963 with
                                         | (bound_typ,(eq_prob,wl')) ->
                                             ((let uu____12029 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____12029
                                               then
                                                 let wl'1 =
                                                   let uu___182_12031 = wl1
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___182_12031.wl_deferred);
                                                     ctr =
                                                       (uu___182_12031.ctr);
                                                     defer_ok =
                                                       (uu___182_12031.defer_ok);
                                                     smt_ok =
                                                       (uu___182_12031.smt_ok);
                                                     tcenv =
                                                       (uu___182_12031.tcenv);
                                                     wl_implicits =
                                                       (uu___182_12031.wl_implicits)
                                                   }  in
                                                 let uu____12032 =
                                                   wl_to_string wl'1  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____12032
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____12035 =
                                                 solve_t env eq_prob
                                                   (let uu___183_12037 = wl'
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___183_12037.wl_deferred);
                                                      ctr =
                                                        (uu___183_12037.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___183_12037.smt_ok);
                                                      tcenv =
                                                        (uu___183_12037.tcenv);
                                                      wl_implicits =
                                                        (uu___183_12037.wl_implicits)
                                                    })
                                                  in
                                               match uu____12035 with
                                               | Success uu____12038 ->
                                                   let wl2 =
                                                     let uu___184_12044 = wl'
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___184_12044.wl_deferred);
                                                       ctr =
                                                         (uu___184_12044.ctr);
                                                       defer_ok =
                                                         (uu___184_12044.defer_ok);
                                                       smt_ok =
                                                         (uu___184_12044.smt_ok);
                                                       tcenv =
                                                         (uu___184_12044.tcenv);
                                                       wl_implicits =
                                                         (uu___184_12044.wl_implicits)
                                                     }  in
                                                   let wl3 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl2
                                                      in
                                                   let uu____12048 =
                                                     FStar_List.fold_left
                                                       (fun wl4  ->
                                                          fun p  ->
                                                            solve_prob' true
                                                              p
                                                              FStar_Pervasives_Native.None
                                                              [] wl4) wl3
                                                       bounds_probs
                                                      in
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    solve env wl3)
                                               | Failed (p,msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    (let uu____12060 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12060
                                                     then
                                                       let uu____12061 =
                                                         let uu____12062 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12062
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12061
                                                     else ());
                                                    (let uu____12068 =
                                                       let uu____12083 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12083)
                                                        in
                                                     match uu____12068 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12105))
                                                         ->
                                                         let uu____12130 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12130
                                                          with
                                                          | (eq_prob1,wl2) ->
                                                              let wl3 =
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                  [] wl2
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl3))
                                                     | (FStar_TypeChecker_Common.Flex_rigid
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          (x,phi)))
                                                         ->
                                                         let uu____12169 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12169
                                                          with
                                                          | (eq_prob1,wl2) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl2 tp x
                                                                  phi
                                                                 in
                                                              let wl3 =
                                                                let uu____12186
                                                                  =
                                                                  let uu____12191
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12191
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12186
                                                                  [] wl2
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl3))
                                                     | uu____12196 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12211 when flip ->
                              let uu____12212 =
                                let uu____12213 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12214 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12213 uu____12214
                                 in
                              failwith uu____12212
                          | uu____12215 ->
                              let uu____12216 =
                                let uu____12217 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12218 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12217 uu____12218
                                 in
                              failwith uu____12216))))

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
                      (fun uu____12246  ->
                         match uu____12246 with
                         | (x,i) ->
                             let uu____12257 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12257, i)) bs_lhs
                     in
                  let uu____12258 = lhs  in
                  match uu____12258 with
                  | (uu____12259,u_lhs,uu____12261) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12374 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12384 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12384, univ)
                             in
                          match uu____12374 with
                          | (k,univ) ->
                              let uu____12397 =
                                let uu____12404 =
                                  let uu____12407 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12407
                                   in
                                copy_uvar u_lhs uu____12404 wl2  in
                              (match uu____12397 with
                               | (uu____12420,u,wl3) ->
                                   let uu____12423 =
                                     let uu____12426 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12426
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12423, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12462 =
                              let uu____12475 =
                                let uu____12484 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12484 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12530  ->
                                   fun uu____12531  ->
                                     match (uu____12530, uu____12531) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12622 =
                                           let uu____12629 =
                                             let uu____12632 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12632
                                              in
                                           copy_uvar u_lhs uu____12629 wl2
                                            in
                                         (match uu____12622 with
                                          | (uu____12655,t_a,wl3) ->
                                              let uu____12658 =
                                                let uu____12665 =
                                                  let uu____12668 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12668
                                                   in
                                                copy_uvar u_lhs uu____12665
                                                  wl3
                                                 in
                                              (match uu____12658 with
                                               | (uu____12683,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12475
                                ([], wl1)
                               in
                            (match uu____12462 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___185_12744 = ct  in
                                   let uu____12745 =
                                     let uu____12748 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12748
                                      in
                                   let uu____12763 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___185_12744.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___185_12744.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12745;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12763;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___185_12744.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___186_12781 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___186_12781.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___186_12781.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12784 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12784 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12838 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12838 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12855 =
                                          let uu____12860 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12860)  in
                                        TERM uu____12855  in
                                      let uu____12861 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12861 with
                                       | (sub_prob,wl3) ->
                                           let uu____12872 =
                                             let uu____12873 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12873
                                              in
                                           solve env uu____12872))
                             | (x,imp)::formals2 ->
                                 let uu____12887 =
                                   let uu____12894 =
                                     let uu____12897 =
                                       let uu____12900 =
                                         let uu____12901 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____12901
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____12900
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____12897
                                      in
                                   copy_uvar u_lhs uu____12894 wl1  in
                                 (match uu____12887 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____12925 =
                                          let uu____12928 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12928
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12925 t_y
                                         in
                                      let uu____12929 =
                                        let uu____12932 =
                                          let uu____12935 =
                                            let uu____12936 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12936, imp)  in
                                          [uu____12935]  in
                                        FStar_List.append bs_terms
                                          uu____12932
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12929 formals2 wl2)
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
              (let uu____12978 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12978
               then
                 let uu____12979 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12980 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12979 (rel_to_string (p_rel orig)) uu____12980
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13085 = rhs wl1 scope env1 subst1  in
                     (match uu____13085 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13105 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13105
                            then
                              let uu____13106 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13106
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___187_13160 = hd1  in
                       let uu____13161 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___187_13160.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___187_13160.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13161
                       }  in
                     let hd21 =
                       let uu___188_13165 = hd2  in
                       let uu____13166 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___188_13165.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___188_13165.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13166
                       }  in
                     let uu____13169 =
                       let uu____13174 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13174
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13169 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13193 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13193
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13197 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13197 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13252 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13252
                                  in
                               ((let uu____13264 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13264
                                 then
                                   let uu____13265 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13266 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13265
                                     uu____13266
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13293 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13322 = aux wl [] env [] bs1 bs2  in
               match uu____13322 with
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
        (let uu____13373 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13373 wl)

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
              let uu____13387 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13387 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13417 = lhs1  in
              match uu____13417 with
              | (uu____13420,ctx_u,uu____13422) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13428 ->
                        let uu____13429 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13429 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13476 = quasi_pattern env1 lhs1  in
              match uu____13476 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13506) ->
                  let uu____13511 = lhs1  in
                  (match uu____13511 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13525 = occurs_check ctx_u rhs1  in
                       (match uu____13525 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13567 =
                                let uu____13574 =
                                  let uu____13575 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13575
                                   in
                                FStar_Util.Inl uu____13574  in
                              (uu____13567, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13595 =
                                 let uu____13596 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13596  in
                               if uu____13595
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13616 =
                                    let uu____13623 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13623  in
                                  let uu____13628 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13616, uu____13628)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13690  ->
                     match uu____13690 with
                     | (x,i) ->
                         let uu____13701 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13701, i)) bs_lhs
                 in
              let uu____13702 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13702 with
              | (rhs_hd,args) ->
                  let uu____13739 = FStar_Util.prefix args  in
                  (match uu____13739 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13797 = lhs1  in
                       (match uu____13797 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13801 =
                              let uu____13812 =
                                let uu____13819 =
                                  let uu____13822 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13822
                                   in
                                copy_uvar u_lhs uu____13819 wl1  in
                              match uu____13812 with
                              | (uu____13843,t_last_arg,wl2) ->
                                  let uu____13846 =
                                    let uu____13853 =
                                      let uu____13856 =
                                        let uu____13863 =
                                          let uu____13870 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____13870]  in
                                        FStar_List.append bs_lhs uu____13863
                                         in
                                      let uu____13887 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____13856
                                        uu____13887
                                       in
                                    copy_uvar u_lhs uu____13853 wl2  in
                                  (match uu____13846 with
                                   | (uu____13900,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13906 =
                                         let uu____13913 =
                                           let uu____13916 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____13916
                                            in
                                         copy_uvar u_lhs uu____13913 wl3  in
                                       (match uu____13906 with
                                        | (uu____13929,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13801 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13953 =
                                     let uu____13954 =
                                       let uu____13959 =
                                         let uu____13960 =
                                           let uu____13963 =
                                             let uu____13968 =
                                               let uu____13969 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13969]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13968
                                              in
                                           uu____13963
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13960
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13959)  in
                                     TERM uu____13954  in
                                   [uu____13953]  in
                                 let uu____13990 =
                                   let uu____13997 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____13997 with
                                   | (p1,wl3) ->
                                       let uu____14014 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14014 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13990 with
                                  | (sub_probs,wl3) ->
                                      let uu____14041 =
                                        let uu____14042 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14042  in
                                      solve env1 uu____14041))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14075 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14075 with
                | (uu____14090,args) ->
                    (match args with | [] -> false | uu____14118 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14133 =
                  let uu____14134 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14134.FStar_Syntax_Syntax.n  in
                match uu____14133 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14137 -> true
                | uu____14150 -> false  in
              let uu____14151 = quasi_pattern env1 lhs1  in
              match uu____14151 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14162 =
                    let uu____14163 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14163
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14162
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14170 = is_app rhs1  in
                  if uu____14170
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14172 = is_arrow rhs1  in
                     if uu____14172
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14174 =
                          let uu____14175 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14175
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14174))
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
                let uu____14178 = lhs  in
                (match uu____14178 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14182 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14182 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14197 =
                              let uu____14200 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14200
                               in
                            FStar_All.pipe_right uu____14197
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14215 = occurs_check ctx_uv rhs1  in
                          (match uu____14215 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14237 =
                                   let uu____14238 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14238
                                    in
                                 giveup_or_defer env orig wl uu____14237
                               else
                                 (let uu____14240 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14240
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14245 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14245
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14247 =
                                         let uu____14248 =
                                           names_to_string1 fvs2  in
                                         let uu____14249 =
                                           names_to_string1 fvs1  in
                                         let uu____14250 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14248 uu____14249
                                           uu____14250
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14247)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14256 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14260 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14260 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14283 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14283
                             | (FStar_Util.Inl msg,uu____14285) ->
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
                  (let uu____14314 =
                     let uu____14331 = quasi_pattern env lhs  in
                     let uu____14338 = quasi_pattern env rhs  in
                     (uu____14331, uu____14338)  in
                   match uu____14314 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14381 = lhs  in
                       (match uu____14381 with
                        | ({ FStar_Syntax_Syntax.n = uu____14382;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14384;_},u_lhs,uu____14386)
                            ->
                            let uu____14389 = rhs  in
                            (match uu____14389 with
                             | (uu____14390,u_rhs,uu____14392) ->
                                 let uu____14393 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14393
                                 then
                                   let uu____14394 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14394
                                 else
                                   (let uu____14396 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14396 with
                                    | (sub_prob,wl1) ->
                                        let uu____14407 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14407 with
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
                                             let uu____14435 =
                                               let uu____14442 =
                                                 let uu____14445 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14445
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
                                                 uu____14442
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14435 with
                                              | (uu____14448,w,wl2) ->
                                                  let w_app =
                                                    let uu____14454 =
                                                      let uu____14459 =
                                                        FStar_List.map
                                                          (fun uu____14468 
                                                             ->
                                                             match uu____14468
                                                             with
                                                             | (z,uu____14474)
                                                                 ->
                                                                 let uu____14475
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14475)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14459
                                                       in
                                                    uu____14454
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14479 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14479
                                                    then
                                                      let uu____14480 =
                                                        let uu____14483 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14484 =
                                                          let uu____14487 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14488 =
                                                            let uu____14491 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14492 =
                                                              let uu____14495
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14500
                                                                =
                                                                let uu____14503
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14508
                                                                  =
                                                                  let uu____14511
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14511]
                                                                   in
                                                                uu____14503
                                                                  ::
                                                                  uu____14508
                                                                 in
                                                              uu____14495 ::
                                                                uu____14500
                                                               in
                                                            uu____14491 ::
                                                              uu____14492
                                                             in
                                                          uu____14487 ::
                                                            uu____14488
                                                           in
                                                        uu____14483 ::
                                                          uu____14484
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14480
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14517 =
                                                          let uu____14522 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14522)
                                                           in
                                                        TERM uu____14517  in
                                                      let uu____14523 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14523
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14528 =
                                                             let uu____14533
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
                                                               uu____14533)
                                                              in
                                                           TERM uu____14528
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14534 =
                                                      let uu____14535 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14535
                                                       in
                                                    solve env uu____14534)))))))
                   | uu____14536 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____14604 = head_matches_delta env1 wl1 t1 t2  in
           match uu____14604 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____14635,uu____14636) ->
                    let rec may_relate head3 =
                      let uu____14663 =
                        let uu____14664 = FStar_Syntax_Subst.compress head3
                           in
                        uu____14664.FStar_Syntax_Syntax.n  in
                      match uu____14663 with
                      | FStar_Syntax_Syntax.Tm_name uu____14667 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____14668 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14691;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____14692;
                            FStar_Syntax_Syntax.fv_qual = uu____14693;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14696;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____14697;
                            FStar_Syntax_Syntax.fv_qual = uu____14698;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____14702,uu____14703) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____14745) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____14751) ->
                          may_relate t
                      | uu____14756 -> false  in
                    let uu____14757 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____14757
                    then
                      let uu____14758 =
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
                                 let uu____14790 =
                                   let uu____14791 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____14791 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____14790
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____14796 = has_type_guard t1 t2  in
                             (uu____14796, wl1)
                           else
                             (let uu____14802 = has_type_guard t2 t1  in
                              (uu____14802, wl1)))
                         in
                      (match uu____14758 with
                       | (guard,wl2) ->
                           let uu____14809 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____14809)
                    else
                      (let uu____14811 =
                         let uu____14812 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14813 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____14812 uu____14813
                          in
                       giveup env1 uu____14811 orig)
                | (uu____14814,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___189_14828 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___189_14828.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___189_14828.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___189_14828.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___189_14828.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___189_14828.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___189_14828.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___189_14828.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___189_14828.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____14829,FStar_Pervasives_Native.None ) ->
                    ((let uu____14841 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14841
                      then
                        let uu____14842 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____14843 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____14844 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____14845 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____14842 uu____14843 uu____14844 uu____14845
                      else ());
                     (let uu____14847 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____14847 with
                      | (head11,args1) ->
                          let uu____14884 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____14884 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____14938 =
                                   let uu____14939 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____14940 = args_to_string args1  in
                                   let uu____14941 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____14942 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____14939 uu____14940 uu____14941
                                     uu____14942
                                    in
                                 giveup env1 uu____14938 orig
                               else
                                 (let uu____14944 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____14951 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____14951 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____14944
                                  then
                                    let uu____14952 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____14952 with
                                    | USolved wl2 ->
                                        let uu____14954 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____14954
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____14958 =
                                       base_and_refinement env1 t1  in
                                     match uu____14958 with
                                     | (base1,refinement1) ->
                                         let uu____14983 =
                                           base_and_refinement env1 t2  in
                                         (match uu____14983 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____15040 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____15040 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____15044 =
                                                          FStar_List.fold_right2
                                                            (fun uu____15077 
                                                               ->
                                                               fun
                                                                 uu____15078 
                                                                 ->
                                                                 fun
                                                                   uu____15079
                                                                    ->
                                                                   match 
                                                                    (uu____15077,
                                                                    uu____15078,
                                                                    uu____15079)
                                                                   with
                                                                   | 
                                                                   ((a,uu____15115),
                                                                    (a',uu____15117),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____15138
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____15138
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
                                                        (match uu____15044
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____15166
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____15166
                                                               then
                                                                 let uu____15167
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____15167
                                                               else ());
                                                              (let formula =
                                                                 let uu____15172
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____15172
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
                                               | uu____15180 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___190_15220 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___190_15220.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15223 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15223
          then
            let uu____15224 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15224
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15229 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15229
              then
                let uu____15230 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15231 =
                  let uu____15232 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15233 =
                    let uu____15234 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15234  in
                  Prims.strcat uu____15232 uu____15233  in
                let uu____15235 =
                  let uu____15236 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15237 =
                    let uu____15238 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15238  in
                  Prims.strcat uu____15236 uu____15237  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15230
                  uu____15231 uu____15235
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15241,uu____15242) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15267,FStar_Syntax_Syntax.Tm_delayed uu____15268) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15293,uu____15294) ->
                  let uu____15321 =
                    let uu___191_15322 = problem  in
                    let uu____15323 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___191_15322.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15323;
                      FStar_TypeChecker_Common.relation =
                        (uu___191_15322.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___191_15322.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___191_15322.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___191_15322.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___191_15322.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___191_15322.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___191_15322.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___191_15322.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15321 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15324,uu____15325) ->
                  let uu____15332 =
                    let uu___192_15333 = problem  in
                    let uu____15334 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___192_15333.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15334;
                      FStar_TypeChecker_Common.relation =
                        (uu___192_15333.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___192_15333.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___192_15333.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___192_15333.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___192_15333.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___192_15333.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___192_15333.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___192_15333.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15332 wl
              | (uu____15335,FStar_Syntax_Syntax.Tm_ascribed uu____15336) ->
                  let uu____15363 =
                    let uu___193_15364 = problem  in
                    let uu____15365 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___193_15364.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___193_15364.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___193_15364.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15365;
                      FStar_TypeChecker_Common.element =
                        (uu___193_15364.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___193_15364.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___193_15364.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___193_15364.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___193_15364.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___193_15364.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15363 wl
              | (uu____15366,FStar_Syntax_Syntax.Tm_meta uu____15367) ->
                  let uu____15374 =
                    let uu___194_15375 = problem  in
                    let uu____15376 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___194_15375.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___194_15375.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___194_15375.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15376;
                      FStar_TypeChecker_Common.element =
                        (uu___194_15375.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___194_15375.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___194_15375.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___194_15375.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___194_15375.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___194_15375.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15374 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15378),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15380)) ->
                  let uu____15389 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15389
              | (FStar_Syntax_Syntax.Tm_bvar uu____15390,uu____15391) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15392,FStar_Syntax_Syntax.Tm_bvar uu____15393) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___146_15452 =
                    match uu___146_15452 with
                    | [] -> c
                    | bs ->
                        let uu____15474 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15474
                     in
                  let uu____15483 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15483 with
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
                                    let uu____15606 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15606
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
                  let mk_t t l uu___147_15681 =
                    match uu___147_15681 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15715 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15715 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____15834 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____15835 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____15834
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____15835 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____15836,uu____15837) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15864 -> true
                    | uu____15881 -> false  in
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
                      (let uu____15922 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___195_15930 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___195_15930.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___195_15930.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___195_15930.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___195_15930.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___195_15930.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___195_15930.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___195_15930.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___195_15930.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___195_15930.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___195_15930.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___195_15930.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___195_15930.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___195_15930.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___195_15930.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___195_15930.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___195_15930.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___195_15930.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___195_15930.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___195_15930.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___195_15930.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___195_15930.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___195_15930.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___195_15930.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___195_15930.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___195_15930.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___195_15930.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___195_15930.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___195_15930.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___195_15930.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___195_15930.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___195_15930.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___195_15930.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___195_15930.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___195_15930.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___195_15930.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15922 with
                       | (uu____15933,ty,uu____15935) ->
                           let uu____15936 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15936)
                     in
                  let uu____15937 =
                    let uu____15950 = maybe_eta t1  in
                    let uu____15955 = maybe_eta t2  in
                    (uu____15950, uu____15955)  in
                  (match uu____15937 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___196_15979 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___196_15979.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___196_15979.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___196_15979.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___196_15979.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___196_15979.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___196_15979.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___196_15979.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___196_15979.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15990 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15990
                       then
                         let uu____15991 = destruct_flex_t not_abs wl  in
                         (match uu____15991 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___197_16006 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___197_16006.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___197_16006.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___197_16006.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___197_16006.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___197_16006.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___197_16006.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___197_16006.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___197_16006.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16018 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16018
                       then
                         let uu____16019 = destruct_flex_t not_abs wl  in
                         (match uu____16019 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___197_16034 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___197_16034.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___197_16034.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___197_16034.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___197_16034.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___197_16034.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___197_16034.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___197_16034.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___197_16034.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16036 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16049,FStar_Syntax_Syntax.Tm_abs uu____16050) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16077 -> true
                    | uu____16094 -> false  in
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
                      (let uu____16135 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___195_16143 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___195_16143.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___195_16143.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___195_16143.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___195_16143.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___195_16143.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___195_16143.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___195_16143.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___195_16143.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___195_16143.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___195_16143.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___195_16143.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___195_16143.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___195_16143.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___195_16143.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___195_16143.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___195_16143.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___195_16143.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___195_16143.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___195_16143.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___195_16143.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___195_16143.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___195_16143.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___195_16143.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___195_16143.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___195_16143.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___195_16143.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___195_16143.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___195_16143.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___195_16143.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___195_16143.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___195_16143.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___195_16143.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___195_16143.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___195_16143.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___195_16143.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16135 with
                       | (uu____16146,ty,uu____16148) ->
                           let uu____16149 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16149)
                     in
                  let uu____16150 =
                    let uu____16163 = maybe_eta t1  in
                    let uu____16168 = maybe_eta t2  in
                    (uu____16163, uu____16168)  in
                  (match uu____16150 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___196_16192 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___196_16192.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___196_16192.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___196_16192.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___196_16192.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___196_16192.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___196_16192.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___196_16192.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___196_16192.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16203 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16203
                       then
                         let uu____16204 = destruct_flex_t not_abs wl  in
                         (match uu____16204 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___197_16219 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___197_16219.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___197_16219.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___197_16219.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___197_16219.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___197_16219.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___197_16219.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___197_16219.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___197_16219.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16231 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16231
                       then
                         let uu____16232 = destruct_flex_t not_abs wl  in
                         (match uu____16232 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___197_16247 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___197_16247.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___197_16247.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___197_16247.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___197_16247.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___197_16247.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___197_16247.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___197_16247.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___197_16247.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16249 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16277 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16277) &&
                       (let uu____16281 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16281))
                      &&
                      (let uu____16288 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16288 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___148_16300 =
                             match uu___148_16300 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16301 -> true
                             | uu____16302 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16303 -> false)
                     in
                  let uu____16304 = as_refinement should_delta env wl t1  in
                  (match uu____16304 with
                   | (x11,phi1) ->
                       let uu____16311 = as_refinement should_delta env wl t2
                          in
                       (match uu____16311 with
                        | (x21,phi21) ->
                            let uu____16318 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16318 with
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
                                   let uu____16384 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16384
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16396 =
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
                                   let uu____16407 =
                                     let uu____16412 =
                                       let uu____16419 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16419]  in
                                     mk_t_problem wl1 uu____16412 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16407 with
                                    | (ref_prob,wl2) ->
                                        let uu____16434 =
                                          solve env1
                                            (let uu___198_16436 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___198_16436.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___198_16436.smt_ok);
                                               tcenv = (uu___198_16436.tcenv);
                                               wl_implicits =
                                                 (uu___198_16436.wl_implicits)
                                             })
                                           in
                                        (match uu____16434 with
                                         | Failed uu____16443 -> fallback ()
                                         | Success uu____16448 ->
                                             let guard =
                                               let uu____16456 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16456
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___199_16465 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___199_16465.attempting);
                                                 wl_deferred =
                                                   (uu___199_16465.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___199_16465.defer_ok);
                                                 smt_ok =
                                                   (uu___199_16465.smt_ok);
                                                 tcenv =
                                                   (uu___199_16465.tcenv);
                                                 wl_implicits =
                                                   (uu___199_16465.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16467,FStar_Syntax_Syntax.Tm_uvar uu____16468) ->
                  let uu____16497 = destruct_flex_t t1 wl  in
                  (match uu____16497 with
                   | (f1,wl1) ->
                       let uu____16504 = destruct_flex_t t2 wl1  in
                       (match uu____16504 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16511;
                    FStar_Syntax_Syntax.pos = uu____16512;
                    FStar_Syntax_Syntax.vars = uu____16513;_},uu____16514),FStar_Syntax_Syntax.Tm_uvar
                 uu____16515) ->
                  let uu____16564 = destruct_flex_t t1 wl  in
                  (match uu____16564 with
                   | (f1,wl1) ->
                       let uu____16571 = destruct_flex_t t2 wl1  in
                       (match uu____16571 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16578,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16579;
                    FStar_Syntax_Syntax.pos = uu____16580;
                    FStar_Syntax_Syntax.vars = uu____16581;_},uu____16582))
                  ->
                  let uu____16631 = destruct_flex_t t1 wl  in
                  (match uu____16631 with
                   | (f1,wl1) ->
                       let uu____16638 = destruct_flex_t t2 wl1  in
                       (match uu____16638 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16645;
                    FStar_Syntax_Syntax.pos = uu____16646;
                    FStar_Syntax_Syntax.vars = uu____16647;_},uu____16648),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16649;
                    FStar_Syntax_Syntax.pos = uu____16650;
                    FStar_Syntax_Syntax.vars = uu____16651;_},uu____16652))
                  ->
                  let uu____16721 = destruct_flex_t t1 wl  in
                  (match uu____16721 with
                   | (f1,wl1) ->
                       let uu____16728 = destruct_flex_t t2 wl1  in
                       (match uu____16728 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16735,uu____16736) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16751 = destruct_flex_t t1 wl  in
                  (match uu____16751 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16758;
                    FStar_Syntax_Syntax.pos = uu____16759;
                    FStar_Syntax_Syntax.vars = uu____16760;_},uu____16761),uu____16762)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16797 = destruct_flex_t t1 wl  in
                  (match uu____16797 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____16804,FStar_Syntax_Syntax.Tm_uvar uu____16805) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____16820,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16821;
                    FStar_Syntax_Syntax.pos = uu____16822;
                    FStar_Syntax_Syntax.vars = uu____16823;_},uu____16824))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16859,FStar_Syntax_Syntax.Tm_arrow uu____16860) ->
                  solve_t' env
                    (let uu___200_16888 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___200_16888.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___200_16888.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___200_16888.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___200_16888.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___200_16888.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___200_16888.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___200_16888.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___200_16888.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___200_16888.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16889;
                    FStar_Syntax_Syntax.pos = uu____16890;
                    FStar_Syntax_Syntax.vars = uu____16891;_},uu____16892),FStar_Syntax_Syntax.Tm_arrow
                 uu____16893) ->
                  solve_t' env
                    (let uu___200_16941 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___200_16941.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___200_16941.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___200_16941.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___200_16941.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___200_16941.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___200_16941.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___200_16941.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___200_16941.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___200_16941.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____16942,FStar_Syntax_Syntax.Tm_uvar uu____16943) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____16958,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16959;
                    FStar_Syntax_Syntax.pos = uu____16960;
                    FStar_Syntax_Syntax.vars = uu____16961;_},uu____16962))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____16997,uu____16998) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17013;
                    FStar_Syntax_Syntax.pos = uu____17014;
                    FStar_Syntax_Syntax.vars = uu____17015;_},uu____17016),uu____17017)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17052,uu____17053) ->
                  let t21 =
                    let uu____17061 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17061  in
                  solve_t env
                    (let uu___201_17087 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___201_17087.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___201_17087.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___201_17087.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___201_17087.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___201_17087.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___201_17087.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___201_17087.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___201_17087.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___201_17087.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17088,FStar_Syntax_Syntax.Tm_refine uu____17089) ->
                  let t11 =
                    let uu____17097 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17097  in
                  solve_t env
                    (let uu___202_17123 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___202_17123.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___202_17123.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___202_17123.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___202_17123.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___202_17123.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___202_17123.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___202_17123.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___202_17123.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___202_17123.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____17200 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____17200 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____17421 = br1  in
                             (match uu____17421 with
                              | (p1,w1,uu____17446) ->
                                  let uu____17463 = br2  in
                                  (match uu____17463 with
                                   | (p2,w2,uu____17482) ->
                                       let uu____17487 =
                                         let uu____17488 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____17488  in
                                       if uu____17487
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____17504 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____17504 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____17537 = br2  in
                                              (match uu____17537 with
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
                                                     let uu____17572 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____17572
                                                      in
                                                   let uu____17583 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____17606,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____17623) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____17666 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____17666
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____17583
                                                     (fun uu____17708  ->
                                                        match uu____17708
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____17729 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____17729
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____17744
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____17744
                                                                   (fun
                                                                    uu____17768
                                                                     ->
                                                                    match uu____17768
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
                         | uu____17853 -> FStar_Pervasives_Native.None  in
                       let uu____17890 = solve_branches wl1 brs1 brs2  in
                       (match uu____17890 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____17921,uu____17922) ->
                  let head1 =
                    let uu____17946 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17946
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17986 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17986
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18026 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18026
                    then
                      let uu____18027 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18028 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18029 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18027 uu____18028 uu____18029
                    else ());
                   (let uu____18031 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18031
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18038 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18038
                       then
                         let uu____18039 =
                           let uu____18046 =
                             let uu____18047 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18047 = FStar_Syntax_Util.Equal  in
                           if uu____18046
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18057 = mk_eq2 wl orig t1 t2  in
                              match uu____18057 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18039 with
                         | (guard,wl1) ->
                             let uu____18078 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18078
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18081,uu____18082) ->
                  let head1 =
                    let uu____18090 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18090
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18130 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18130
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18170 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18170
                    then
                      let uu____18171 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18172 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18173 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18171 uu____18172 uu____18173
                    else ());
                   (let uu____18175 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18175
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18182 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18182
                       then
                         let uu____18183 =
                           let uu____18190 =
                             let uu____18191 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18191 = FStar_Syntax_Util.Equal  in
                           if uu____18190
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18201 = mk_eq2 wl orig t1 t2  in
                              match uu____18201 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18183 with
                         | (guard,wl1) ->
                             let uu____18222 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18222
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18225,uu____18226) ->
                  let head1 =
                    let uu____18228 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18228
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18268 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18268
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18308 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18308
                    then
                      let uu____18309 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18310 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18311 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18309 uu____18310 uu____18311
                    else ());
                   (let uu____18313 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18313
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18320 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18320
                       then
                         let uu____18321 =
                           let uu____18328 =
                             let uu____18329 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18329 = FStar_Syntax_Util.Equal  in
                           if uu____18328
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18339 = mk_eq2 wl orig t1 t2  in
                              match uu____18339 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18321 with
                         | (guard,wl1) ->
                             let uu____18360 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18360
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18363,uu____18364) ->
                  let head1 =
                    let uu____18366 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18366
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18406 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18406
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18446 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18446
                    then
                      let uu____18447 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18448 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18449 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18447 uu____18448 uu____18449
                    else ());
                   (let uu____18451 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18451
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18458 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18458
                       then
                         let uu____18459 =
                           let uu____18466 =
                             let uu____18467 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18467 = FStar_Syntax_Util.Equal  in
                           if uu____18466
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18477 = mk_eq2 wl orig t1 t2  in
                              match uu____18477 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18459 with
                         | (guard,wl1) ->
                             let uu____18498 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18498
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18501,uu____18502) ->
                  let head1 =
                    let uu____18504 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18504
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18544 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18544
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18584 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18584
                    then
                      let uu____18585 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18586 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18587 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18585 uu____18586 uu____18587
                    else ());
                   (let uu____18589 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18589
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18596 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18596
                       then
                         let uu____18597 =
                           let uu____18604 =
                             let uu____18605 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18605 = FStar_Syntax_Util.Equal  in
                           if uu____18604
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18615 = mk_eq2 wl orig t1 t2  in
                              match uu____18615 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18597 with
                         | (guard,wl1) ->
                             let uu____18636 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18636
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____18639,uu____18640) ->
                  let head1 =
                    let uu____18656 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18656
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18696 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18696
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18736 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18736
                    then
                      let uu____18737 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18738 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18739 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18737 uu____18738 uu____18739
                    else ());
                   (let uu____18741 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18741
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18748 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18748
                       then
                         let uu____18749 =
                           let uu____18756 =
                             let uu____18757 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18757 = FStar_Syntax_Util.Equal  in
                           if uu____18756
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18767 = mk_eq2 wl orig t1 t2  in
                              match uu____18767 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18749 with
                         | (guard,wl1) ->
                             let uu____18788 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18788
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18791,FStar_Syntax_Syntax.Tm_match uu____18792) ->
                  let head1 =
                    let uu____18816 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18816
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18856 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18856
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18896 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18896
                    then
                      let uu____18897 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18898 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18899 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18897 uu____18898 uu____18899
                    else ());
                   (let uu____18901 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18901
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18908 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18908
                       then
                         let uu____18909 =
                           let uu____18916 =
                             let uu____18917 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18917 = FStar_Syntax_Util.Equal  in
                           if uu____18916
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18927 = mk_eq2 wl orig t1 t2  in
                              match uu____18927 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18909 with
                         | (guard,wl1) ->
                             let uu____18948 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18948
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18951,FStar_Syntax_Syntax.Tm_uinst uu____18952) ->
                  let head1 =
                    let uu____18960 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18960
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19000 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19000
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19040 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19040
                    then
                      let uu____19041 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19042 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19043 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19041 uu____19042 uu____19043
                    else ());
                   (let uu____19045 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19045
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19052 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19052
                       then
                         let uu____19053 =
                           let uu____19060 =
                             let uu____19061 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19061 = FStar_Syntax_Util.Equal  in
                           if uu____19060
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19071 = mk_eq2 wl orig t1 t2  in
                              match uu____19071 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19053 with
                         | (guard,wl1) ->
                             let uu____19092 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19092
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19095,FStar_Syntax_Syntax.Tm_name uu____19096) ->
                  let head1 =
                    let uu____19098 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19098
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19138 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19138
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19178 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19178
                    then
                      let uu____19179 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19180 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19181 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19179 uu____19180 uu____19181
                    else ());
                   (let uu____19183 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19183
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19190 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19190
                       then
                         let uu____19191 =
                           let uu____19198 =
                             let uu____19199 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19199 = FStar_Syntax_Util.Equal  in
                           if uu____19198
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19209 = mk_eq2 wl orig t1 t2  in
                              match uu____19209 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19191 with
                         | (guard,wl1) ->
                             let uu____19230 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19230
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19233,FStar_Syntax_Syntax.Tm_constant uu____19234) ->
                  let head1 =
                    let uu____19236 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19236
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19276 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19276
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19316 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19316
                    then
                      let uu____19317 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19318 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19319 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19317 uu____19318 uu____19319
                    else ());
                   (let uu____19321 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19321
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19328 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19328
                       then
                         let uu____19329 =
                           let uu____19336 =
                             let uu____19337 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19337 = FStar_Syntax_Util.Equal  in
                           if uu____19336
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19347 = mk_eq2 wl orig t1 t2  in
                              match uu____19347 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19329 with
                         | (guard,wl1) ->
                             let uu____19368 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19368
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19371,FStar_Syntax_Syntax.Tm_fvar uu____19372) ->
                  let head1 =
                    let uu____19374 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19374
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19414 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19414
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19454 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19454
                    then
                      let uu____19455 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19456 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19457 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19455 uu____19456 uu____19457
                    else ());
                   (let uu____19459 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19459
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19466 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19466
                       then
                         let uu____19467 =
                           let uu____19474 =
                             let uu____19475 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19475 = FStar_Syntax_Util.Equal  in
                           if uu____19474
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19485 = mk_eq2 wl orig t1 t2  in
                              match uu____19485 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19467 with
                         | (guard,wl1) ->
                             let uu____19506 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19506
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19509,FStar_Syntax_Syntax.Tm_app uu____19510) ->
                  let head1 =
                    let uu____19526 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19526
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19566 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19566
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19606 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19606
                    then
                      let uu____19607 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19608 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19609 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19607 uu____19608 uu____19609
                    else ());
                   (let uu____19611 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19611
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19618 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19618
                       then
                         let uu____19619 =
                           let uu____19626 =
                             let uu____19627 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19627 = FStar_Syntax_Util.Equal  in
                           if uu____19626
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19637 = mk_eq2 wl orig t1 t2  in
                              match uu____19637 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19619 with
                         | (guard,wl1) ->
                             let uu____19658 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19658
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____19661,FStar_Syntax_Syntax.Tm_let uu____19662) ->
                  let uu____19687 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____19687
                  then
                    let uu____19688 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____19688
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____19690,uu____19691) ->
                  let uu____19704 =
                    let uu____19709 =
                      let uu____19710 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19711 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19712 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19713 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19710 uu____19711 uu____19712 uu____19713
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19709)
                     in
                  FStar_Errors.raise_error uu____19704
                    t1.FStar_Syntax_Syntax.pos
              | (uu____19714,FStar_Syntax_Syntax.Tm_let uu____19715) ->
                  let uu____19728 =
                    let uu____19733 =
                      let uu____19734 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19735 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19736 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19737 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19734 uu____19735 uu____19736 uu____19737
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19733)
                     in
                  FStar_Errors.raise_error uu____19728
                    t1.FStar_Syntax_Syntax.pos
              | uu____19738 -> giveup env "head tag mismatch" orig))))

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
          (let uu____19797 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____19797
           then
             let uu____19798 =
               let uu____19799 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____19799  in
             let uu____19800 =
               let uu____19801 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____19801  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____19798 uu____19800
           else ());
          (let uu____19803 =
             let uu____19804 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____19804  in
           if uu____19803
           then
             let uu____19805 =
               let uu____19806 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____19807 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____19806 uu____19807
                in
             giveup env uu____19805 orig
           else
             (let uu____19809 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____19809 with
              | (ret_sub_prob,wl1) ->
                  let uu____19816 =
                    FStar_List.fold_right2
                      (fun uu____19849  ->
                         fun uu____19850  ->
                           fun uu____19851  ->
                             match (uu____19849, uu____19850, uu____19851)
                             with
                             | ((a1,uu____19887),(a2,uu____19889),(arg_sub_probs,wl2))
                                 ->
                                 let uu____19910 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____19910 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____19816 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____19939 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____19939  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____19969 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____19972)::[] -> wp1
              | uu____19989 ->
                  let uu____19998 =
                    let uu____19999 =
                      let uu____20000 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20000  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____19999
                     in
                  failwith uu____19998
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20006 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20006]
              | x -> x  in
            let uu____20008 =
              let uu____20017 =
                let uu____20024 =
                  let uu____20025 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20025 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20024  in
              [uu____20017]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20008;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20038 = lift_c1 ()  in solve_eq uu____20038 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___149_20044  ->
                       match uu___149_20044 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20045 -> false))
                in
             let uu____20046 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20072)::uu____20073,(wp2,uu____20075)::uu____20076)
                   -> (wp1, wp2)
               | uu____20129 ->
                   let uu____20150 =
                     let uu____20155 =
                       let uu____20156 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20157 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20156 uu____20157
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20155)
                      in
                   FStar_Errors.raise_error uu____20150
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20046 with
             | (wpc1,wpc2) ->
                 let uu____20164 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20164
                 then
                   let uu____20167 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20167 wl
                 else
                   (let uu____20169 =
                      let uu____20176 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20176  in
                    match uu____20169 with
                    | (c2_decl,qualifiers) ->
                        let uu____20197 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20197
                        then
                          let c1_repr =
                            let uu____20201 =
                              let uu____20202 =
                                let uu____20203 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20203  in
                              let uu____20204 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20202 uu____20204
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20201
                             in
                          let c2_repr =
                            let uu____20206 =
                              let uu____20207 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20208 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20207 uu____20208
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20206
                             in
                          let uu____20209 =
                            let uu____20214 =
                              let uu____20215 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20216 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20215 uu____20216
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20214
                             in
                          (match uu____20209 with
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
                                 ((let uu____20230 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20230
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20233 =
                                     let uu____20240 =
                                       let uu____20241 =
                                         let uu____20256 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20259 =
                                           let uu____20268 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20275 =
                                             let uu____20284 =
                                               let uu____20291 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20291
                                                in
                                             [uu____20284]  in
                                           uu____20268 :: uu____20275  in
                                         (uu____20256, uu____20259)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20241
                                        in
                                     FStar_Syntax_Syntax.mk uu____20240  in
                                   uu____20233 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20326 =
                                    let uu____20333 =
                                      let uu____20334 =
                                        let uu____20349 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20352 =
                                          let uu____20361 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20368 =
                                            let uu____20377 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20384 =
                                              let uu____20393 =
                                                let uu____20400 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20400
                                                 in
                                              [uu____20393]  in
                                            uu____20377 :: uu____20384  in
                                          uu____20361 :: uu____20368  in
                                        (uu____20349, uu____20352)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20334
                                       in
                                    FStar_Syntax_Syntax.mk uu____20333  in
                                  uu____20326 FStar_Pervasives_Native.None r)
                              in
                           let uu____20438 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20438 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20446 =
                                   let uu____20449 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____20449
                                    in
                                 solve_prob orig uu____20446 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____20456 = FStar_Util.physical_equality c1 c2  in
        if uu____20456
        then
          let uu____20457 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20457
        else
          ((let uu____20460 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20460
            then
              let uu____20461 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20462 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20461
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20462
            else ());
           (let uu____20464 =
              let uu____20473 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20476 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20473, uu____20476)  in
            match uu____20464 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20494),FStar_Syntax_Syntax.Total
                    (t2,uu____20496)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20513 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20513 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20514,FStar_Syntax_Syntax.Total uu____20515) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20533),FStar_Syntax_Syntax.Total
                    (t2,uu____20535)) ->
                     let uu____20552 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20552 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20554),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20556)) ->
                     let uu____20573 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20573 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20575),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20577)) ->
                     let uu____20594 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20594 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20595,FStar_Syntax_Syntax.Comp uu____20596) ->
                     let uu____20605 =
                       let uu___203_20608 = problem  in
                       let uu____20611 =
                         let uu____20612 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20612
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___203_20608.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20611;
                         FStar_TypeChecker_Common.relation =
                           (uu___203_20608.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___203_20608.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___203_20608.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___203_20608.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___203_20608.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___203_20608.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___203_20608.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___203_20608.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20605 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20613,FStar_Syntax_Syntax.Comp uu____20614) ->
                     let uu____20623 =
                       let uu___203_20626 = problem  in
                       let uu____20629 =
                         let uu____20630 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20630
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___203_20626.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20629;
                         FStar_TypeChecker_Common.relation =
                           (uu___203_20626.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___203_20626.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___203_20626.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___203_20626.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___203_20626.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___203_20626.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___203_20626.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___203_20626.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20623 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20631,FStar_Syntax_Syntax.GTotal uu____20632) ->
                     let uu____20641 =
                       let uu___204_20644 = problem  in
                       let uu____20647 =
                         let uu____20648 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20648
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___204_20644.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___204_20644.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___204_20644.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20647;
                         FStar_TypeChecker_Common.element =
                           (uu___204_20644.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___204_20644.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___204_20644.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___204_20644.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___204_20644.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___204_20644.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20641 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20649,FStar_Syntax_Syntax.Total uu____20650) ->
                     let uu____20659 =
                       let uu___204_20662 = problem  in
                       let uu____20665 =
                         let uu____20666 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20666
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___204_20662.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___204_20662.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___204_20662.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20665;
                         FStar_TypeChecker_Common.element =
                           (uu___204_20662.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___204_20662.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___204_20662.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___204_20662.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___204_20662.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___204_20662.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20659 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20667,FStar_Syntax_Syntax.Comp uu____20668) ->
                     let uu____20669 =
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
                     if uu____20669
                     then
                       let uu____20670 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____20670 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20674 =
                            let uu____20679 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____20679
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20685 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____20686 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____20685, uu____20686))
                             in
                          match uu____20674 with
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
                           (let uu____20693 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____20693
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20695 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____20695 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20698 =
                                  let uu____20699 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____20700 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____20699 uu____20700
                                   in
                                giveup env uu____20698 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____20707 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20735  ->
              match uu____20735 with
              | (uu____20744,tm,uu____20746,uu____20747) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____20707 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____20780 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____20780 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____20798 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____20826  ->
                match uu____20826 with
                | (u1,u2) ->
                    let uu____20833 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____20834 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____20833 uu____20834))
         in
      FStar_All.pipe_right uu____20798 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____20861,[])) -> "{}"
      | uu____20886 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____20909 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____20909
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____20912 =
              FStar_List.map
                (fun uu____20922  ->
                   match uu____20922 with
                   | (uu____20927,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____20912 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____20932 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____20932 imps
  
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
                  let uu____20985 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____20985
                  then
                    let uu____20986 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____20987 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____20986
                      (rel_to_string rel) uu____20987
                  else "TOP"  in
                let uu____20989 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____20989 with
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
              let uu____21046 =
                let uu____21049 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____21049
                 in
              FStar_Syntax_Syntax.new_bv uu____21046 t1  in
            let uu____21052 =
              let uu____21057 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21057
               in
            match uu____21052 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____21113 = FStar_Options.eager_inference ()  in
          if uu____21113
          then
            let uu___205_21114 = probs  in
            {
              attempting = (uu___205_21114.attempting);
              wl_deferred = (uu___205_21114.wl_deferred);
              ctr = (uu___205_21114.ctr);
              defer_ok = false;
              smt_ok = (uu___205_21114.smt_ok);
              tcenv = (uu___205_21114.tcenv);
              wl_implicits = (uu___205_21114.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21134 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21134
              then
                let uu____21135 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21135
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
          ((let uu____21157 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21157
            then
              let uu____21158 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21158
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21162 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21162
             then
               let uu____21163 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21163
             else ());
            (let f2 =
               let uu____21166 =
                 let uu____21167 = FStar_Syntax_Util.unmeta f1  in
                 uu____21167.FStar_Syntax_Syntax.n  in
               match uu____21166 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21171 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___206_21172 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___206_21172.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___206_21172.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___206_21172.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred,(Prims.string,FStar_Syntax_Syntax.term,
                                           FStar_Syntax_Syntax.ctx_uvar,
                                           FStar_Range.range)
                                           FStar_Pervasives_Native.tuple4
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
            let uu____21274 =
              let uu____21275 =
                let uu____21276 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21276;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21275  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____21274
  
let with_guard_no_simp :
  'Auu____21291 .
    'Auu____21291 ->
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
            let uu____21314 =
              let uu____21315 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21315;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21314
  
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
          (let uu____21353 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21353
           then
             let uu____21354 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21355 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21354
               uu____21355
           else ());
          (let uu____21357 =
             let uu____21362 = empty_worklist env  in
             let uu____21363 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____21362 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____21363
              in
           match uu____21357 with
           | (prob,wl) ->
               let g =
                 let uu____21371 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21389  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21371  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21431 = try_teq true env t1 t2  in
        match uu____21431 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21435 = FStar_TypeChecker_Env.get_range env  in
              let uu____21436 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21435 uu____21436);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21443 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21443
              then
                let uu____21444 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21445 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21446 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21444
                  uu____21445 uu____21446
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
          let uu____21468 = FStar_TypeChecker_Env.get_range env  in
          let uu____21469 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21468 uu____21469
  
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
        (let uu____21494 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21494
         then
           let uu____21495 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21496 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21495 uu____21496
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21499 =
           let uu____21506 = empty_worklist env  in
           let uu____21507 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____21506 env c1 rel c2 FStar_Pervasives_Native.None
             uu____21507 "sub_comp"
            in
         match uu____21499 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21517 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21535  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21517)
  
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
      fun uu____21588  ->
        match uu____21588 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21631 =
                 let uu____21636 =
                   let uu____21637 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21638 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21637 uu____21638
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21636)  in
               let uu____21639 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21631 uu____21639)
               in
            let equiv1 v1 v' =
              let uu____21651 =
                let uu____21656 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21657 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21656, uu____21657)  in
              match uu____21651 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21676 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21706 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____21706 with
                      | FStar_Syntax_Syntax.U_unif uu____21713 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21742  ->
                                    match uu____21742 with
                                    | (u,v') ->
                                        let uu____21751 = equiv1 v1 v'  in
                                        if uu____21751
                                        then
                                          let uu____21754 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____21754 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____21770 -> []))
               in
            let uu____21775 =
              let wl =
                let uu___207_21779 = empty_worklist env  in
                {
                  attempting = (uu___207_21779.attempting);
                  wl_deferred = (uu___207_21779.wl_deferred);
                  ctr = (uu___207_21779.ctr);
                  defer_ok = false;
                  smt_ok = (uu___207_21779.smt_ok);
                  tcenv = (uu___207_21779.tcenv);
                  wl_implicits = (uu___207_21779.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21797  ->
                      match uu____21797 with
                      | (lb,v1) ->
                          let uu____21804 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____21804 with
                           | USolved wl1 -> ()
                           | uu____21806 -> fail1 lb v1)))
               in
            let rec check_ineq uu____21816 =
              match uu____21816 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21825) -> true
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
                      uu____21848,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21850,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21861) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21868,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21876 -> false)
               in
            let uu____21881 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21896  ->
                      match uu____21896 with
                      | (u,v1) ->
                          let uu____21903 = check_ineq (u, v1)  in
                          if uu____21903
                          then true
                          else
                            ((let uu____21906 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____21906
                              then
                                let uu____21907 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____21908 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____21907
                                  uu____21908
                              else ());
                             false)))
               in
            if uu____21881
            then ()
            else
              ((let uu____21912 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____21912
                then
                  ((let uu____21914 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21914);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21924 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21924))
                else ());
               (let uu____21934 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____21934))
  
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
        let fail1 uu____22001 =
          match uu____22001 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___208_22022 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___208_22022.attempting);
            wl_deferred = (uu___208_22022.wl_deferred);
            ctr = (uu___208_22022.ctr);
            defer_ok;
            smt_ok = (uu___208_22022.smt_ok);
            tcenv = (uu___208_22022.tcenv);
            wl_implicits = (uu___208_22022.wl_implicits)
          }  in
        (let uu____22024 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22024
         then
           let uu____22025 = FStar_Util.string_of_bool defer_ok  in
           let uu____22026 = wl_to_string wl  in
           let uu____22027 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22025 uu____22026 uu____22027
         else ());
        (let g1 =
           let uu____22038 = solve_and_commit env wl fail1  in
           match uu____22038 with
           | FStar_Pervasives_Native.Some
               (uu____22045::uu____22046,uu____22047) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___209_22072 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___209_22072.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___209_22072.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22081 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___210_22089 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___210_22089.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___210_22089.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___210_22089.FStar_TypeChecker_Env.implicits)
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
    let uu____22137 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22137 with
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
            let uu___211_22260 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___211_22260.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___211_22260.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___211_22260.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22261 =
            let uu____22262 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22262  in
          if uu____22261
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22270 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22271 =
                       let uu____22272 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22272
                        in
                     FStar_Errors.diag uu____22270 uu____22271)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22276 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22277 =
                        let uu____22278 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22278
                         in
                      FStar_Errors.diag uu____22276 uu____22277)
                   else ();
                   (let uu____22281 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22281 "discharge_guard'"
                      env vc1);
                   (let uu____22282 = check_trivial vc1  in
                    match uu____22282 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22289 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22290 =
                                let uu____22291 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22291
                                 in
                              FStar_Errors.diag uu____22289 uu____22290)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22296 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22297 =
                                let uu____22298 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22298
                                 in
                              FStar_Errors.diag uu____22296 uu____22297)
                           else ();
                           (let vcs =
                              let uu____22311 = FStar_Options.use_tactics ()
                                 in
                              if uu____22311
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22333  ->
                                     (let uu____22335 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____22335);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22378  ->
                                              match uu____22378 with
                                              | (env1,goal,opts) ->
                                                  let uu____22394 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22394, opts)))))
                              else
                                (let uu____22396 =
                                   let uu____22403 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22403)  in
                                 [uu____22396])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22440  ->
                                    match uu____22440 with
                                    | (env1,goal,opts) ->
                                        let uu____22456 = check_trivial goal
                                           in
                                        (match uu____22456 with
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
                                                (let uu____22464 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22465 =
                                                   let uu____22466 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22467 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22466 uu____22467
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22464 uu____22465)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22470 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22471 =
                                                   let uu____22472 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22472
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22470 uu____22471)
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
      let uu____22486 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22486 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22493 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22493
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22504 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22504 with
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
          let unresolved ctx_u =
            let uu____22537 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____22537 with
            | FStar_Pervasives_Native.Some uu____22540 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____22560 = acc  in
            match uu____22560 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22612 = hd1  in
                     (match uu____22612 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____22626 = unresolved ctx_u  in
                             if uu____22626
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___212_22638 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___212_22638.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___212_22638.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___212_22638.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___212_22638.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___212_22638.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___212_22638.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___212_22638.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___212_22638.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___212_22638.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___212_22638.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___212_22638.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___212_22638.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___212_22638.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___212_22638.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___212_22638.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___212_22638.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___212_22638.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___212_22638.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___212_22638.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___212_22638.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___212_22638.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___212_22638.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___212_22638.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___212_22638.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___212_22638.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___212_22638.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___212_22638.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___212_22638.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___212_22638.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___212_22638.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___212_22638.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___212_22638.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___212_22638.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___212_22638.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___212_22638.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___212_22638.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___212_22638.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___213_22641 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___213_22641.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___213_22641.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___213_22641.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___213_22641.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___213_22641.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___213_22641.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___213_22641.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___213_22641.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___213_22641.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___213_22641.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___213_22641.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___213_22641.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___213_22641.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___213_22641.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___213_22641.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___213_22641.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___213_22641.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___213_22641.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___213_22641.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___213_22641.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___213_22641.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___213_22641.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___213_22641.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___213_22641.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___213_22641.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___213_22641.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___213_22641.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___213_22641.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___213_22641.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___213_22641.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___213_22641.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___213_22641.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___213_22641.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___213_22641.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___213_22641.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___213_22641.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___213_22641.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____22644 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22644
                                   then
                                     let uu____22645 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____22646 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____22647 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____22648 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____22645 uu____22646 uu____22647
                                       reason uu____22648
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____22659 =
                                             let uu____22668 =
                                               let uu____22675 =
                                                 let uu____22676 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____22677 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 FStar_Util.format2
                                                   "Failed while checking implicit %s set to %s"
                                                   uu____22676 uu____22677
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____22675, r)
                                                in
                                             [uu____22668]  in
                                           FStar_Errors.add_errors
                                             uu____22659);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___216_22691 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___216_22691.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___216_22691.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___216_22691.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____22694 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____22704  ->
                                               let uu____22705 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____22706 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____22707 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____22705 uu____22706
                                                 reason uu____22707)) env2 g2
                                         true
                                        in
                                     match uu____22694 with
                                     | FStar_Pervasives_Native.Some g3 -> g3
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Env.implicits
                                         out), true) tl1)))))
             in
          let uu___217_22717 = g  in
          let uu____22718 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___217_22717.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___217_22717.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___217_22717.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____22718
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
        let uu____22768 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____22768 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22777 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____22777
      | (reason,e,ctx_u,r)::uu____22782 ->
          let uu____22801 =
            let uu____22806 =
              let uu____22807 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____22808 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____22807 uu____22808 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____22806)
             in
          FStar_Errors.raise_error uu____22801 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___218_22819 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___218_22819.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___218_22819.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___218_22819.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____22834 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22834 with
      | FStar_Pervasives_Native.Some uu____22840 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22856 = try_teq false env t1 t2  in
        match uu____22856 with
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
        (let uu____22890 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22890
         then
           let uu____22891 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____22892 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22891
             uu____22892
         else ());
        (let uu____22894 =
           let uu____22901 = empty_worklist env  in
           new_t_prob uu____22901 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____22894 with
         | (prob,x,wl) ->
             let g =
               let uu____22914 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____22932  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____22914  in
             ((let uu____22960 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____22960
               then
                 let uu____22961 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____22962 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____22963 =
                   let uu____22964 = FStar_Util.must g  in
                   guard_to_string env uu____22964  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____22961 uu____22962 uu____22963
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
        let uu____22998 = check_subtyping env t1 t2  in
        match uu____22998 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23017 =
              let uu____23018 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23018 g  in
            FStar_Pervasives_Native.Some uu____23017
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23036 = check_subtyping env t1 t2  in
        match uu____23036 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23055 =
              let uu____23056 =
                let uu____23057 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23057]  in
              close_guard env uu____23056 g  in
            FStar_Pervasives_Native.Some uu____23055
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23086 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23086
         then
           let uu____23087 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23088 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23087
             uu____23088
         else ());
        (let uu____23090 =
           let uu____23097 = empty_worklist env  in
           new_t_prob uu____23097 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23090 with
         | (prob,x,wl) ->
             let g =
               let uu____23104 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23122  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23104  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23151 =
                      let uu____23152 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23152]  in
                    close_guard env uu____23151 g1  in
                  discharge_guard_nosmt env g2))
  