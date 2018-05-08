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
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1897 = FStar_Syntax_Util.type_u ()  in
          match uu____1897 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1909 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1909 with
               | (uu____1920,tt,wl1) ->
                   let uu____1923 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1923, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___131_1928  ->
    match uu___131_1928 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1944 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1944 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1956  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2054 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2054 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2054 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2054 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2120 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2120  in
                  let uu____2123 =
                    let uu____2130 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2130
                      guard_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2123 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2151 ->
                            let uu____2158 =
                              let uu____2163 =
                                FStar_List.map
                                  (fun uu____2176  ->
                                     match uu____2176 with
                                     | (x,i) ->
                                         let uu____2187 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2187, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2163  in
                            uu____2158 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2190 =
                        let uu____2193 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2193;
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
                      (uu____2190, wl1)
  
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
                  let uu____2256 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2256 with
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
                  let uu____2333 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2333 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2368 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2368 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2368 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2368 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2419 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2474 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2474]  in
                        let uu____2487 =
                          let uu____2490 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2490  in
                        let uu____2493 =
                          let uu____2496 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2496  in
                        (bs, uu____2487, uu____2493)
                     in
                  match uu____2419 with
                  | (bs,lg_ty,elt) ->
                      let uu____2536 =
                        let uu____2543 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___163_2551 = wl  in
                           {
                             attempting = (uu___163_2551.attempting);
                             wl_deferred = (uu___163_2551.wl_deferred);
                             ctr = (uu___163_2551.ctr);
                             defer_ok = (uu___163_2551.defer_ok);
                             smt_ok = (uu___163_2551.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___163_2551.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2543
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2536 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2563 =
                                   let uu____2568 =
                                     let uu____2569 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2569]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2568
                                    in
                                 uu____2563 FStar_Pervasives_Native.None loc
                              in
                           let uu____2590 =
                             let uu____2593 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2593;
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
                           (uu____2590, wl1))
  
let problem_using_guard :
  'Auu____2610 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2610 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2610 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2610 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2647 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2647;
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
  'Auu____2658 .
    worklist ->
      'Auu____2658 FStar_TypeChecker_Common.problem ->
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
        let uu____2708 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2708
        then
          let uu____2709 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2710 = prob_to_string env d  in
          let uu____2711 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2709 uu____2710 uu____2711 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2717 -> failwith "impossible"  in
           let uu____2718 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2730 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2731 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2730, uu____2731)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2735 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2736 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2735, uu____2736)
              in
           match uu____2718 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___132_2754  ->
            match uu___132_2754 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2766 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___133_2788  ->
           match uu___133_2788 with
           | UNIV uu____2791 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2798 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2798
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
        (fun uu___134_2822  ->
           match uu___134_2822 with
           | UNIV (u',t) ->
               let uu____2827 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2827
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2831 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2842 =
        let uu____2843 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2843
         in
      FStar_Syntax_Subst.compress uu____2842
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2854 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2854
  
let norm_arg :
  'Auu____2861 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2861) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2861)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2884 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2884, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2925  ->
              match uu____2925 with
              | (x,imp) ->
                  let uu____2936 =
                    let uu___164_2937 = x  in
                    let uu____2938 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___164_2937.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___164_2937.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2938
                    }  in
                  (uu____2936, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2959 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2959
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2963 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2963
        | uu____2966 -> u2  in
      let uu____2967 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2967
  
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
                (let uu____3081 = norm_refinement env t12  in
                 match uu____3081 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3096;
                     FStar_Syntax_Syntax.vars = uu____3097;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3123 =
                       let uu____3124 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3125 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3124 uu____3125
                        in
                     failwith uu____3123)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3139 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3139
          | FStar_Syntax_Syntax.Tm_uinst uu____3140 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3175 =
                   let uu____3176 = FStar_Syntax_Subst.compress t1'  in
                   uu____3176.FStar_Syntax_Syntax.n  in
                 match uu____3175 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3191 -> aux true t1'
                 | uu____3198 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3213 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3242 =
                   let uu____3243 = FStar_Syntax_Subst.compress t1'  in
                   uu____3243.FStar_Syntax_Syntax.n  in
                 match uu____3242 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3258 -> aux true t1'
                 | uu____3265 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3280 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3323 =
                   let uu____3324 = FStar_Syntax_Subst.compress t1'  in
                   uu____3324.FStar_Syntax_Syntax.n  in
                 match uu____3323 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3339 -> aux true t1'
                 | uu____3346 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3361 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3376 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3391 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3406 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3421 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3448 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3479 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3500 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3529 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3556 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3593 ->
              let uu____3600 =
                let uu____3601 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3602 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3601 uu____3602
                 in
              failwith uu____3600
          | FStar_Syntax_Syntax.Tm_ascribed uu____3615 ->
              let uu____3642 =
                let uu____3643 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3644 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3643 uu____3644
                 in
              failwith uu____3642
          | FStar_Syntax_Syntax.Tm_delayed uu____3657 ->
              let uu____3682 =
                let uu____3683 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3684 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3683 uu____3684
                 in
              failwith uu____3682
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3697 =
                let uu____3698 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3699 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3698 uu____3699
                 in
              failwith uu____3697
           in
        let uu____3712 = whnf env t1  in aux false uu____3712
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3743 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3743 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3774 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3774 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3810 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3810, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3821 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3821 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3846 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3846 with
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
  fun uu____3923  ->
    match uu____3923 with
    | (t_base,refopt) ->
        let uu____3956 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3956 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3996 =
      let uu____3999 =
        let uu____4002 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4025  ->
                  match uu____4025 with | (uu____4032,uu____4033,x) -> x))
           in
        FStar_List.append wl.attempting uu____4002  in
      FStar_List.map (wl_prob_to_string wl) uu____3999  in
    FStar_All.pipe_right uu____3996 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____4047 .
    ('Auu____4047,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4058  ->
    match uu____4058 with
    | (uu____4065,c,args) ->
        let uu____4068 = print_ctx_uvar c  in
        let uu____4069 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4068 uu____4069
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4075 = FStar_Syntax_Util.head_and_args t  in
    match uu____4075 with
    | (head1,_args) ->
        let uu____4112 =
          let uu____4113 = FStar_Syntax_Subst.compress head1  in
          uu____4113.FStar_Syntax_Syntax.n  in
        (match uu____4112 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4116 -> true
         | uu____4131 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4137 = FStar_Syntax_Util.head_and_args t  in
    match uu____4137 with
    | (head1,_args) ->
        let uu____4174 =
          let uu____4175 = FStar_Syntax_Subst.compress head1  in
          uu____4175.FStar_Syntax_Syntax.n  in
        (match uu____4174 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4179) -> u
         | uu____4200 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4223 = FStar_Syntax_Util.head_and_args t  in
      match uu____4223 with
      | (head1,args) ->
          let uu____4264 =
            let uu____4265 = FStar_Syntax_Subst.compress head1  in
            uu____4265.FStar_Syntax_Syntax.n  in
          (match uu____4264 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4273)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4316 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___135_4341  ->
                         match uu___135_4341 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4345 =
                               let uu____4346 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4346.FStar_Syntax_Syntax.n  in
                             (match uu____4345 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4350 -> false)
                         | uu____4351 -> true))
                  in
               (match uu____4316 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4373 =
                        FStar_List.collect
                          (fun uu___136_4379  ->
                             match uu___136_4379 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4383 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4383]
                             | uu____4384 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4373 FStar_List.rev  in
                    let uu____4393 =
                      let uu____4400 =
                        let uu____4407 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___137_4421  ->
                                  match uu___137_4421 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4425 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4425]
                                  | uu____4426 -> []))
                           in
                        FStar_All.pipe_right uu____4407 FStar_List.rev  in
                      let uu____4443 =
                        let uu____4446 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4446  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4400 uu____4443
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4393 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4475  ->
                                match uu____4475 with
                                | (x,i) ->
                                    let uu____4486 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4486, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4509  ->
                                match uu____4509 with
                                | (a,i) ->
                                    let uu____4520 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4520, i)) args_sol
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
           | uu____4536 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4556 =
          let uu____4569 =
            let uu____4570 = FStar_Syntax_Subst.compress k  in
            uu____4570.FStar_Syntax_Syntax.n  in
          match uu____4569 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4623 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4623)
              else
                (let uu____4637 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4637 with
                 | (ys',t1,uu____4660) ->
                     let uu____4665 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4665))
          | uu____4706 ->
              let uu____4707 =
                let uu____4718 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4718)  in
              ((ys, t), uu____4707)
           in
        match uu____4556 with
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
                 let uu____4767 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4767 c  in
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
               (let uu____4841 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4841
                then
                  let uu____4842 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4843 = print_ctx_uvar uv  in
                  let uu____4844 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4842 uu____4843 uu____4844
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
             let uu____4850 = p_guard_uvar prob  in
             match uu____4850 with
             | (xs,uv) ->
                 let fail1 uu____4862 =
                   let uu____4863 =
                     let uu____4864 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4865 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4864 uu____4865
                      in
                   failwith uu____4863  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____4915  ->
                           match uu____4915 with
                           | (a,i) ->
                               let uu____4928 =
                                 let uu____4929 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____4929.FStar_Syntax_Syntax.n  in
                               (match uu____4928 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____4947 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____4955 =
                     let uu____4956 = is_flex g  in
                     Prims.op_Negation uu____4956  in
                   if uu____4955
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____4960 = destruct_flex_t g wl  in
                      match uu____4960 with
                      | ((uu____4965,uv1,args),wl1) ->
                          ((let uu____4970 = args_as_binders args  in
                            assign_solution uu____4970 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___165_4972 = wl1  in
                   {
                     attempting = (uu___165_4972.attempting);
                     wl_deferred = (uu___165_4972.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___165_4972.defer_ok);
                     smt_ok = (uu___165_4972.smt_ok);
                     tcenv = (uu___165_4972.tcenv);
                     wl_implicits = (uu___165_4972.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4993 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4993
         then
           let uu____4994 = FStar_Util.string_of_int pid  in
           let uu____4995 =
             let uu____4996 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4996 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4994 uu____4995
         else ());
        commit sol;
        (let uu___166_5003 = wl  in
         {
           attempting = (uu___166_5003.attempting);
           wl_deferred = (uu___166_5003.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___166_5003.defer_ok);
           smt_ok = (uu___166_5003.smt_ok);
           tcenv = (uu___166_5003.tcenv);
           wl_implicits = (uu___166_5003.wl_implicits)
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
             | (uu____5065,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5091 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5091
              in
           (let uu____5097 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5097
            then
              let uu____5098 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5099 =
                let uu____5100 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5100 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5098 uu____5099
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
        let uu____5125 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5125 FStar_Util.set_elements  in
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
      let uu____5159 = occurs uk t  in
      match uu____5159 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5188 =
                 let uu____5189 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5190 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5189 uu____5190
                  in
               FStar_Pervasives_Native.Some uu____5188)
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
            let uu____5279 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5279 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5323 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5371  ->
             match uu____5371 with
             | (x,uu____5381) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5394 = FStar_List.last bs  in
      match uu____5394 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5412) ->
          let uu____5417 =
            FStar_Util.prefix_until
              (fun uu___138_5432  ->
                 match uu___138_5432 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5434 -> false) g
             in
          (match uu____5417 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5447,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5483 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5483 with
        | (pfx,uu____5493) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5505 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5505 with
             | (uu____5512,src',wl1) ->
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
                 | uu____5612 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5613 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5667  ->
                  fun uu____5668  ->
                    match (uu____5667, uu____5668) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5749 =
                          let uu____5750 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5750
                           in
                        if uu____5749
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5775 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5775
                           then
                             let uu____5788 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5788)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5613 with | (isect,uu____5825) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5854 'Auu____5855 .
    (FStar_Syntax_Syntax.bv,'Auu____5854) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5855) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5912  ->
              fun uu____5913  ->
                match (uu____5912, uu____5913) with
                | ((a,uu____5931),(b,uu____5933)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5948 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5948) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5978  ->
           match uu____5978 with
           | (y,uu____5984) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5995 'Auu____5996 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5995) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5996)
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
                   let uu____6105 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6105
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____6113 =
                        let uu____6116 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____6116 :: seen  in
                      aux uu____6113 args2)
               | uu____6117 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6147 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____6184 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6190 -> false
  
let string_of_option :
  'Auu____6197 .
    ('Auu____6197 -> Prims.string) ->
      'Auu____6197 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___139_6212  ->
      match uu___139_6212 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6218 = f x  in Prims.strcat "Some " uu____6218
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___140_6223  ->
    match uu___140_6223 with
    | MisMatch (d1,d2) ->
        let uu____6234 =
          let uu____6235 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6236 =
            let uu____6237 =
              let uu____6238 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6238 ")"  in
            Prims.strcat ") (" uu____6237  in
          Prims.strcat uu____6235 uu____6236  in
        Prims.strcat "MisMatch (" uu____6234
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___141_6243  ->
    match uu___141_6243 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____6258 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____6288 = m2 ()  in
          (match uu____6288 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____6303 -> HeadMatch)
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
          let uu____6317 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6317 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6328 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6351 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6360 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6388 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6388
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6389 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6390 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6391 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6406 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6419 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6443) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6449,uu____6450) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6492) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6513;
             FStar_Syntax_Syntax.index = uu____6514;
             FStar_Syntax_Syntax.sort = t2;_},uu____6516)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6523 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6524 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6525 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6538 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6545 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6563 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6563
  
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
            let uu____6590 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6590
            then FullMatch
            else
              (let uu____6592 =
                 let uu____6601 =
                   let uu____6604 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6604  in
                 let uu____6605 =
                   let uu____6608 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6608  in
                 (uu____6601, uu____6605)  in
               MisMatch uu____6592)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6614),FStar_Syntax_Syntax.Tm_uinst (g,uu____6616)) ->
            let uu____6625 = head_matches env f g  in
            FStar_All.pipe_right uu____6625 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6628 = FStar_Const.eq_const c d  in
            if uu____6628
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6635),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6637)) ->
            let uu____6678 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6678
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6685),FStar_Syntax_Syntax.Tm_refine (y,uu____6687)) ->
            let uu____6696 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6696 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6698),uu____6699) ->
            let uu____6704 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6704 head_match
        | (uu____6705,FStar_Syntax_Syntax.Tm_refine (x,uu____6707)) ->
            let uu____6712 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6712 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6713,FStar_Syntax_Syntax.Tm_type
           uu____6714) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6715,FStar_Syntax_Syntax.Tm_arrow uu____6716) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6742),FStar_Syntax_Syntax.Tm_app (head',uu____6744))
            ->
            let uu____6785 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6785 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6787),uu____6788) ->
            let uu____6809 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6809 head_match
        | (uu____6810,FStar_Syntax_Syntax.Tm_app (head1,uu____6812)) ->
            let uu____6833 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6833 head_match
        | uu____6834 ->
            let uu____6839 =
              let uu____6848 = delta_depth_of_term env t11  in
              let uu____6851 = delta_depth_of_term env t21  in
              (uu____6848, uu____6851)  in
            MisMatch uu____6839
  
let head_matches_delta :
  'Auu____6868 .
    FStar_TypeChecker_Env.env ->
      'Auu____6868 ->
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
            let uu____6915 = FStar_Syntax_Util.head_and_args t  in
            match uu____6915 with
            | (head1,uu____6933) ->
                let uu____6954 =
                  let uu____6955 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6955.FStar_Syntax_Syntax.n  in
                (match uu____6954 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6961 =
                       let uu____6962 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6962 FStar_Option.isSome
                        in
                     if uu____6961
                     then
                       let uu____6981 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6981
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6985 -> FStar_Pervasives_Native.None)
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
              let uu____7118 =
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
              match uu____7118 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____7163 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____7163 with
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
                 uu____7195),uu____7196)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7214 =
                     let uu____7223 = maybe_inline t11  in
                     let uu____7226 = maybe_inline t21  in
                     (uu____7223, uu____7226)  in
                   match uu____7214 with
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
                (uu____7263,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____7264))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7282 =
                     let uu____7291 = maybe_inline t11  in
                     let uu____7294 = maybe_inline t21  in
                     (uu____7291, uu____7294)  in
                   match uu____7282 with
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
            | MisMatch uu____7343 -> fail1 r
            | uu____7352 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7365 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7365
           then
             let uu____7366 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7367 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7368 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7375 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7393 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7393
                    (fun uu____7427  ->
                       match uu____7427 with
                       | (t11,t21) ->
                           let uu____7434 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7435 =
                             let uu____7436 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7436  in
                           Prims.strcat uu____7434 uu____7435))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____7366
               uu____7367 uu____7368 uu____7375
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7448 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7448 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___142_7461  ->
    match uu___142_7461 with
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
      let uu___167_7498 = p  in
      let uu____7501 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7502 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___167_7498.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7501;
        FStar_TypeChecker_Common.relation =
          (uu___167_7498.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7502;
        FStar_TypeChecker_Common.element =
          (uu___167_7498.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___167_7498.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___167_7498.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___167_7498.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___167_7498.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___167_7498.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7516 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7516
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____7521 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7543 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7543 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7551 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7551 with
           | (lh,lhs_args) ->
               let uu____7592 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7592 with
                | (rh,rhs_args) ->
                    let uu____7633 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7646,FStar_Syntax_Syntax.Tm_uvar uu____7647)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7728 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7751,uu____7752)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7770 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7770.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7770.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7770.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7770.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7770.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7770.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7770.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7770.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7770.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7773,FStar_Syntax_Syntax.Tm_uvar uu____7774)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7792 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7792.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7792.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7792.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7792.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7792.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7792.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7792.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7792.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7792.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7795,FStar_Syntax_Syntax.Tm_arrow uu____7796)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7826 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7826.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7826.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7826.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7826.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7826.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7826.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7826.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7826.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7826.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7829,FStar_Syntax_Syntax.Tm_type uu____7830)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7848 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7848.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7848.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7848.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7848.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7848.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7848.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7848.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7848.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7848.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7851,FStar_Syntax_Syntax.Tm_uvar uu____7852)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7870 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7870.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7870.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7870.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7870.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7870.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7870.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7870.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7870.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7870.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7873,FStar_Syntax_Syntax.Tm_uvar uu____7874)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7891,uu____7892)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7909,FStar_Syntax_Syntax.Tm_uvar uu____7910)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7927,uu____7928) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7633 with
                     | (rank,tp1) ->
                         let uu____7941 =
                           FStar_All.pipe_right
                             (let uu___170_7945 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___170_7945.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___170_7945.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___170_7945.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___170_7945.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___170_7945.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___170_7945.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___170_7945.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___170_7945.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___170_7945.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7941))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7951 =
            FStar_All.pipe_right
              (let uu___171_7955 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___171_7955.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___171_7955.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___171_7955.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___171_7955.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___171_7955.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___171_7955.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___171_7955.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___171_7955.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___171_7955.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7951)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8016 probs =
      match uu____8016 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8097 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8118 = rank wl.tcenv hd1  in
               (match uu____8118 with
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
                      (let uu____8177 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8181 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8181)
                          in
                       if uu____8177
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
          let uu____8249 = FStar_Syntax_Util.head_and_args t  in
          match uu____8249 with
          | (hd1,uu____8265) ->
              let uu____8286 =
                let uu____8287 = FStar_Syntax_Subst.compress hd1  in
                uu____8287.FStar_Syntax_Syntax.n  in
              (match uu____8286 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8291) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8325  ->
                           match uu____8325 with
                           | (y,uu____8331) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8345  ->
                                       match uu____8345 with
                                       | (x,uu____8351) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8352 -> false)
           in
        let uu____8353 = rank tcenv p  in
        match uu____8353 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8360 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8387 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8401 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8415 -> false
  
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
                        let uu____8467 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8467 with
                        | (k,uu____8473) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8483 -> false)))
            | uu____8484 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8536 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8542 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8542 = (Prims.parse_int "0")))
                           in
                        if uu____8536 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8558 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8564 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8564 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8558)
               in
            let uu____8565 = filter1 u12  in
            let uu____8568 = filter1 u22  in (uu____8565, uu____8568)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8597 = filter_out_common_univs us1 us2  in
                (match uu____8597 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8656 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8656 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8659 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8669 =
                          let uu____8670 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8671 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8670
                            uu____8671
                           in
                        UFailed uu____8669))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8695 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8695 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8721 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8721 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8724 ->
                let uu____8729 =
                  let uu____8730 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8731 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8730
                    uu____8731 msg
                   in
                UFailed uu____8729
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8732,uu____8733) ->
              let uu____8734 =
                let uu____8735 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8736 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8735 uu____8736
                 in
              failwith uu____8734
          | (FStar_Syntax_Syntax.U_unknown ,uu____8737) ->
              let uu____8738 =
                let uu____8739 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8740 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8739 uu____8740
                 in
              failwith uu____8738
          | (uu____8741,FStar_Syntax_Syntax.U_bvar uu____8742) ->
              let uu____8743 =
                let uu____8744 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8745 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8744 uu____8745
                 in
              failwith uu____8743
          | (uu____8746,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8747 =
                let uu____8748 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8749 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8748 uu____8749
                 in
              failwith uu____8747
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8773 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8773
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8787 = occurs_univ v1 u3  in
              if uu____8787
              then
                let uu____8788 =
                  let uu____8789 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8790 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8789 uu____8790
                   in
                try_umax_components u11 u21 uu____8788
              else
                (let uu____8792 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8792)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8804 = occurs_univ v1 u3  in
              if uu____8804
              then
                let uu____8805 =
                  let uu____8806 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8807 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8806 uu____8807
                   in
                try_umax_components u11 u21 uu____8805
              else
                (let uu____8809 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8809)
          | (FStar_Syntax_Syntax.U_max uu____8810,uu____8811) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8817 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8817
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8819,FStar_Syntax_Syntax.U_max uu____8820) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8826 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8826
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8828,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8829,FStar_Syntax_Syntax.U_name
             uu____8830) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8831) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8832) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8833,FStar_Syntax_Syntax.U_succ
             uu____8834) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8835,FStar_Syntax_Syntax.U_zero
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
      let uu____8935 = bc1  in
      match uu____8935 with
      | (bs1,mk_cod1) ->
          let uu____8979 = bc2  in
          (match uu____8979 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9090 = aux xs ys  in
                     (match uu____9090 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9173 =
                       let uu____9180 = mk_cod1 xs  in ([], uu____9180)  in
                     let uu____9183 =
                       let uu____9190 = mk_cod2 ys  in ([], uu____9190)  in
                     (uu____9173, uu____9183)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____9213 'Auu____9214 'Auu____9215 .
    ('Auu____9213,'Auu____9214,'Auu____9215 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___143_9228  ->
    match uu___143_9228 with
    | (uu____9237,uu____9238,[]) -> true
    | uu____9241 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9272 = f  in
      match uu____9272 with
      | (uu____9279,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9280;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9281;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9284;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9285;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9286;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9338  ->
                 match uu____9338 with
                 | (y,uu____9344) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9466 =
                  let uu____9479 =
                    let uu____9482 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9482  in
                  ((FStar_List.rev pat_binders), uu____9479)  in
                FStar_Pervasives_Native.Some uu____9466
            | (uu____9509,[]) ->
                let uu____9532 =
                  let uu____9545 =
                    let uu____9548 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9548  in
                  ((FStar_List.rev pat_binders), uu____9545)  in
                FStar_Pervasives_Native.Some uu____9532
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9613 =
                  let uu____9614 = FStar_Syntax_Subst.compress a  in
                  uu____9614.FStar_Syntax_Syntax.n  in
                (match uu____9613 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9632 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9632
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___172_9653 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___172_9653.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___172_9653.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9657 =
                            let uu____9658 =
                              let uu____9665 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9665)  in
                            FStar_Syntax_Syntax.NT uu____9658  in
                          [uu____9657]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___173_9677 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___173_9677.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___173_9677.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9678 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9706 =
                  let uu____9719 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9719  in
                (match uu____9706 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9782 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9809 ->
               let uu____9810 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9810 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10086 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10086
       then
         let uu____10087 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10087
       else ());
      (let uu____10089 = next_prob probs  in
       match uu____10089 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___174_10116 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___174_10116.wl_deferred);
               ctr = (uu___174_10116.ctr);
               defer_ok = (uu___174_10116.defer_ok);
               smt_ok = (uu___174_10116.smt_ok);
               tcenv = (uu___174_10116.tcenv);
               wl_implicits = (uu___174_10116.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10123 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10123
                then
                  let uu____10124 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10124
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
                          (let uu___175_10129 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___175_10129.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___175_10129.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___175_10129.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___175_10129.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___175_10129.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___175_10129.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___175_10129.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___175_10129.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___175_10129.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10151 ->
                let uu____10160 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10219  ->
                          match uu____10219 with
                          | (c,uu____10227,uu____10228) -> c < probs.ctr))
                   in
                (match uu____10160 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10269 =
                            let uu____10274 =
                              FStar_List.map
                                (fun uu____10289  ->
                                   match uu____10289 with
                                   | (uu____10300,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10274, (probs.wl_implicits))  in
                          Success uu____10269
                      | uu____10303 ->
                          let uu____10312 =
                            let uu___176_10313 = probs  in
                            let uu____10314 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10333  ->
                                      match uu____10333 with
                                      | (uu____10340,uu____10341,y) -> y))
                               in
                            {
                              attempting = uu____10314;
                              wl_deferred = rest;
                              ctr = (uu___176_10313.ctr);
                              defer_ok = (uu___176_10313.defer_ok);
                              smt_ok = (uu___176_10313.smt_ok);
                              tcenv = (uu___176_10313.tcenv);
                              wl_implicits = (uu___176_10313.wl_implicits)
                            }  in
                          solve env uu____10312))))

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
            let uu____10348 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10348 with
            | USolved wl1 ->
                let uu____10350 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10350
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
                  let uu____10402 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10402 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10405 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10417;
                  FStar_Syntax_Syntax.vars = uu____10418;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10421;
                  FStar_Syntax_Syntax.vars = uu____10422;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10434,uu____10435) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10442,FStar_Syntax_Syntax.Tm_uinst uu____10443) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10450 -> USolved wl

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
            ((let uu____10460 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10460
              then
                let uu____10461 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10461 msg
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
              let uu____10546 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10546 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10598 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10598
               then
                 let uu____10599 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10600 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10599
                   uu____10600
               else ());
              (let uu____10602 = head_matches_delta env1 () t1 t2  in
               match uu____10602 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____10647 ->
                        let uu____10656 = eq_prob t1 t2 wl2  in
                        (match uu____10656 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____10703 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10718 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10719 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10718, uu____10719)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10724 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10725 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10724, uu____10725)
                           in
                        (match uu____10703 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10756 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10756 with
                               | (t1_hd,t1_args) ->
                                   let uu____10795 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10795 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____10849 =
                                             let uu____10856 =
                                               let uu____10865 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____10865 :: t1_args  in
                                             let uu____10878 =
                                               let uu____10885 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____10885 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____10926  ->
                                                  fun uu____10927  ->
                                                    fun uu____10928  ->
                                                      match (uu____10926,
                                                              uu____10927,
                                                              uu____10928)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____10970),
                                                         (a2,uu____10972)) ->
                                                          let uu____10997 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____10997
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____10856
                                               uu____10878
                                              in
                                           match uu____10849 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___177_11023 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___177_11023.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___177_11023.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11039 =
                                                 solve env1 wl'  in
                                               (match uu____11039 with
                                                | Success (uu____11042,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___178_11046 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___178_11046.attempting);
                                                           wl_deferred =
                                                             (uu___178_11046.wl_deferred);
                                                           ctr =
                                                             (uu___178_11046.ctr);
                                                           defer_ok =
                                                             (uu___178_11046.defer_ok);
                                                           smt_ok =
                                                             (uu___178_11046.smt_ok);
                                                           tcenv =
                                                             (uu___178_11046.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11055 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11087 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11087 with
                               | (t1_base,p1_opt) ->
                                   let uu____11128 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11128 with
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
                                              let uu____11259 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____11259
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
                                              let uu____11289 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11289
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
                                              let uu____11319 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11319
                                          | uu____11322 -> t_base  in
                                        let uu____11339 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11339 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11353 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11353, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11360 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11360 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11401 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11401 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11442 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11442
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
                             let uu____11466 = combine t11 t21 wl2  in
                             (match uu____11466 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11499 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11499
                                    then
                                      let uu____11500 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11500
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11539 ts1 =
              match uu____11539 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11602 = pairwise out t wl2  in
                       (match uu____11602 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11638 =
              let uu____11649 = FStar_List.hd ts  in (uu____11649, [], wl1)
               in
            let uu____11658 = FStar_List.tl ts  in
            aux uu____11638 uu____11658  in
          let uu____11665 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11665 with
          | (this_flex,this_rigid) ->
              let uu____11677 =
                let uu____11678 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11678.FStar_Syntax_Syntax.n  in
              (match uu____11677 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11699 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11699
                   then
                     let uu____11700 = destruct_flex_t this_flex wl  in
                     (match uu____11700 with
                      | (flex,wl1) ->
                          let uu____11707 = quasi_pattern env flex  in
                          (match uu____11707 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11725 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11725
                                 then
                                   let uu____11726 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11726
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
                             ((let uu___179_11731 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___179_11731.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___179_11731.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___179_11731.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___179_11731.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___179_11731.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___179_11731.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___179_11731.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___179_11731.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___179_11731.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11732 ->
                   ((let uu____11734 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11734
                     then
                       let uu____11735 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11735
                     else ());
                    (let uu____11737 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11737 with
                     | (u,_args) ->
                         let uu____11774 =
                           let uu____11775 = FStar_Syntax_Subst.compress u
                              in
                           uu____11775.FStar_Syntax_Syntax.n  in
                         (match uu____11774 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____11806 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____11806 with
                                | (u',uu____11822) ->
                                    let uu____11843 =
                                      let uu____11844 = whnf env u'  in
                                      uu____11844.FStar_Syntax_Syntax.n  in
                                    (match uu____11843 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____11869 -> false)
                                 in
                              let uu____11870 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___144_11893  ->
                                        match uu___144_11893 with
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
                                             | uu____11902 -> false)
                                        | uu____11905 -> false))
                                 in
                              (match uu____11870 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____11919 = whnf env this_rigid
                                        in
                                     let uu____11920 =
                                       FStar_List.collect
                                         (fun uu___145_11926  ->
                                            match uu___145_11926 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____11932 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____11932]
                                            | uu____11934 -> []) bounds_probs
                                        in
                                     uu____11919 :: uu____11920  in
                                   let uu____11935 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____11935 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____11966 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____11981 =
                                              let uu____11982 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____11982.FStar_Syntax_Syntax.n
                                               in
                                            match uu____11981 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____11994 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____11994)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____12003 -> bound  in
                                          let uu____12004 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____12004)  in
                                        (match uu____11966 with
                                         | (bound_typ,(eq_prob,wl')) ->
                                             ((let uu____12032 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____12032
                                               then
                                                 let wl'1 =
                                                   let uu___180_12034 = wl1
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___180_12034.wl_deferred);
                                                     ctr =
                                                       (uu___180_12034.ctr);
                                                     defer_ok =
                                                       (uu___180_12034.defer_ok);
                                                     smt_ok =
                                                       (uu___180_12034.smt_ok);
                                                     tcenv =
                                                       (uu___180_12034.tcenv);
                                                     wl_implicits =
                                                       (uu___180_12034.wl_implicits)
                                                   }  in
                                                 let uu____12035 =
                                                   wl_to_string wl'1  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____12035
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____12038 =
                                                 solve_t env eq_prob
                                                   (let uu___181_12040 = wl'
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___181_12040.wl_deferred);
                                                      ctr =
                                                        (uu___181_12040.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___181_12040.smt_ok);
                                                      tcenv =
                                                        (uu___181_12040.tcenv);
                                                      wl_implicits =
                                                        (uu___181_12040.wl_implicits)
                                                    })
                                                  in
                                               match uu____12038 with
                                               | Success uu____12041 ->
                                                   let wl2 =
                                                     let uu___182_12047 = wl'
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___182_12047.wl_deferred);
                                                       ctr =
                                                         (uu___182_12047.ctr);
                                                       defer_ok =
                                                         (uu___182_12047.defer_ok);
                                                       smt_ok =
                                                         (uu___182_12047.smt_ok);
                                                       tcenv =
                                                         (uu___182_12047.tcenv);
                                                       wl_implicits =
                                                         (uu___182_12047.wl_implicits)
                                                     }  in
                                                   let wl3 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl2
                                                      in
                                                   let uu____12051 =
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
                                                    (let uu____12063 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12063
                                                     then
                                                       let uu____12064 =
                                                         let uu____12065 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12065
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12064
                                                     else ());
                                                    (let uu____12071 =
                                                       let uu____12086 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12086)
                                                        in
                                                     match uu____12071 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12108))
                                                         ->
                                                         let uu____12133 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12133
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
                                                         let uu____12172 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12172
                                                          with
                                                          | (eq_prob1,wl2) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl2 tp x
                                                                  phi
                                                                 in
                                                              let wl3 =
                                                                let uu____12189
                                                                  =
                                                                  let uu____12194
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12194
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12189
                                                                  [] wl2
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl3))
                                                     | uu____12199 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12214 when flip ->
                              let uu____12215 =
                                let uu____12216 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12217 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12216 uu____12217
                                 in
                              failwith uu____12215
                          | uu____12218 ->
                              let uu____12219 =
                                let uu____12220 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12221 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12220 uu____12221
                                 in
                              failwith uu____12219))))

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
                      (fun uu____12249  ->
                         match uu____12249 with
                         | (x,i) ->
                             let uu____12260 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12260, i)) bs_lhs
                     in
                  let uu____12261 = lhs  in
                  match uu____12261 with
                  | (uu____12262,u_lhs,uu____12264) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12377 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12387 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12387, univ)
                             in
                          match uu____12377 with
                          | (k,univ) ->
                              let uu____12400 =
                                let uu____12407 =
                                  let uu____12410 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12410
                                   in
                                copy_uvar u_lhs uu____12407 wl2  in
                              (match uu____12400 with
                               | (uu____12423,u,wl3) ->
                                   let uu____12426 =
                                     let uu____12429 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12429
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12426, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12465 =
                              let uu____12478 =
                                let uu____12487 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12487 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12533  ->
                                   fun uu____12534  ->
                                     match (uu____12533, uu____12534) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12625 =
                                           let uu____12632 =
                                             let uu____12635 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12635
                                              in
                                           copy_uvar u_lhs uu____12632 wl2
                                            in
                                         (match uu____12625 with
                                          | (uu____12658,t_a,wl3) ->
                                              let uu____12661 =
                                                let uu____12668 =
                                                  let uu____12671 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12671
                                                   in
                                                copy_uvar u_lhs uu____12668
                                                  wl3
                                                 in
                                              (match uu____12661 with
                                               | (uu____12686,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12478
                                ([], wl1)
                               in
                            (match uu____12465 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___183_12747 = ct  in
                                   let uu____12748 =
                                     let uu____12751 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12751
                                      in
                                   let uu____12766 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___183_12747.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___183_12747.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12748;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12766;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___183_12747.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___184_12784 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___184_12784.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___184_12784.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12787 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12787 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12841 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12841 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12858 =
                                          let uu____12863 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12863)  in
                                        TERM uu____12858  in
                                      let uu____12864 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12864 with
                                       | (sub_prob,wl3) ->
                                           let uu____12875 =
                                             let uu____12876 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12876
                                              in
                                           solve env uu____12875))
                             | (x,imp)::formals2 ->
                                 let uu____12890 =
                                   let uu____12897 =
                                     let uu____12900 =
                                       let uu____12903 =
                                         let uu____12904 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____12904
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____12903
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____12900
                                      in
                                   copy_uvar u_lhs uu____12897 wl1  in
                                 (match uu____12890 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____12928 =
                                          let uu____12931 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12931
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12928 t_y
                                         in
                                      let uu____12932 =
                                        let uu____12935 =
                                          let uu____12938 =
                                            let uu____12939 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12939, imp)  in
                                          [uu____12938]  in
                                        FStar_List.append bs_terms
                                          uu____12935
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12932 formals2 wl2)
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
              (let uu____12981 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12981
               then
                 let uu____12982 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12983 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12982 (rel_to_string (p_rel orig)) uu____12983
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13088 = rhs wl1 scope env1 subst1  in
                     (match uu____13088 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13108 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13108
                            then
                              let uu____13109 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13109
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___185_13163 = hd1  in
                       let uu____13164 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___185_13163.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___185_13163.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13164
                       }  in
                     let hd21 =
                       let uu___186_13168 = hd2  in
                       let uu____13169 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___186_13168.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___186_13168.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13169
                       }  in
                     let uu____13172 =
                       let uu____13177 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13177
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13172 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13196 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13196
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13200 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13200 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13255 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13255
                                  in
                               ((let uu____13267 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13267
                                 then
                                   let uu____13268 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13269 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13268
                                     uu____13269
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13296 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13325 = aux wl [] env [] bs1 bs2  in
               match uu____13325 with
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
        (let uu____13376 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13376 wl)

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
              let uu____13390 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13390 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13420 = lhs1  in
              match uu____13420 with
              | (uu____13423,ctx_u,uu____13425) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13431 ->
                        let uu____13432 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13432 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13479 = quasi_pattern env1 lhs1  in
              match uu____13479 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13509) ->
                  let uu____13514 = lhs1  in
                  (match uu____13514 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13528 = occurs_check ctx_u rhs1  in
                       (match uu____13528 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13570 =
                                let uu____13577 =
                                  let uu____13578 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13578
                                   in
                                FStar_Util.Inl uu____13577  in
                              (uu____13570, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13598 =
                                 let uu____13599 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13599  in
                               if uu____13598
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13619 =
                                    let uu____13626 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13626  in
                                  let uu____13631 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13619, uu____13631)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13693  ->
                     match uu____13693 with
                     | (x,i) ->
                         let uu____13704 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13704, i)) bs_lhs
                 in
              let uu____13705 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13705 with
              | (rhs_hd,args) ->
                  let uu____13742 = FStar_Util.prefix args  in
                  (match uu____13742 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13800 = lhs1  in
                       (match uu____13800 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13804 =
                              let uu____13815 =
                                let uu____13822 =
                                  let uu____13825 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13825
                                   in
                                copy_uvar u_lhs uu____13822 wl1  in
                              match uu____13815 with
                              | (uu____13846,t_last_arg,wl2) ->
                                  let uu____13849 =
                                    let uu____13856 =
                                      let uu____13859 =
                                        let uu____13866 =
                                          let uu____13873 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____13873]  in
                                        FStar_List.append bs_lhs uu____13866
                                         in
                                      let uu____13890 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____13859
                                        uu____13890
                                       in
                                    copy_uvar u_lhs uu____13856 wl2  in
                                  (match uu____13849 with
                                   | (uu____13903,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13909 =
                                         let uu____13916 =
                                           let uu____13919 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____13919
                                            in
                                         copy_uvar u_lhs uu____13916 wl3  in
                                       (match uu____13909 with
                                        | (uu____13932,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13804 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13956 =
                                     let uu____13957 =
                                       let uu____13962 =
                                         let uu____13963 =
                                           let uu____13966 =
                                             let uu____13971 =
                                               let uu____13972 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13972]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13971
                                              in
                                           uu____13966
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13963
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13962)  in
                                     TERM uu____13957  in
                                   [uu____13956]  in
                                 let uu____13993 =
                                   let uu____14000 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14000 with
                                   | (p1,wl3) ->
                                       let uu____14017 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14017 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13993 with
                                  | (sub_probs,wl3) ->
                                      let uu____14044 =
                                        let uu____14045 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14045  in
                                      solve env1 uu____14044))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14078 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14078 with
                | (uu____14093,args) ->
                    (match args with | [] -> false | uu____14121 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14136 =
                  let uu____14137 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14137.FStar_Syntax_Syntax.n  in
                match uu____14136 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14140 -> true
                | uu____14153 -> false  in
              let uu____14154 = quasi_pattern env1 lhs1  in
              match uu____14154 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14165 =
                    let uu____14166 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14166
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14165
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14173 = is_app rhs1  in
                  if uu____14173
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14175 = is_arrow rhs1  in
                     if uu____14175
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14177 =
                          let uu____14178 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14178
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14177))
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
                let uu____14181 = lhs  in
                (match uu____14181 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14185 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14185 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14200 =
                              let uu____14203 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14203
                               in
                            FStar_All.pipe_right uu____14200
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14218 = occurs_check ctx_uv rhs1  in
                          (match uu____14218 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14240 =
                                   let uu____14241 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14241
                                    in
                                 giveup_or_defer env orig wl uu____14240
                               else
                                 (let uu____14243 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14243
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14248 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14248
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14250 =
                                         let uu____14251 =
                                           names_to_string1 fvs2  in
                                         let uu____14252 =
                                           names_to_string1 fvs1  in
                                         let uu____14253 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14251 uu____14252
                                           uu____14253
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14250)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14259 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14263 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14263 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14286 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14286
                             | (FStar_Util.Inl msg,uu____14288) ->
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
                  (let uu____14317 =
                     let uu____14334 = quasi_pattern env lhs  in
                     let uu____14341 = quasi_pattern env rhs  in
                     (uu____14334, uu____14341)  in
                   match uu____14317 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14384 = lhs  in
                       (match uu____14384 with
                        | ({ FStar_Syntax_Syntax.n = uu____14385;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14387;_},u_lhs,uu____14389)
                            ->
                            let uu____14392 = rhs  in
                            (match uu____14392 with
                             | (uu____14393,u_rhs,uu____14395) ->
                                 let uu____14396 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14396
                                 then
                                   let uu____14397 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14397
                                 else
                                   (let uu____14399 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14399 with
                                    | (sub_prob,wl1) ->
                                        let uu____14410 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14410 with
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
                                             let uu____14438 =
                                               let uu____14445 =
                                                 let uu____14448 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14448
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
                                                 uu____14445
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14438 with
                                              | (uu____14451,w,wl2) ->
                                                  let w_app =
                                                    let uu____14457 =
                                                      let uu____14462 =
                                                        FStar_List.map
                                                          (fun uu____14471 
                                                             ->
                                                             match uu____14471
                                                             with
                                                             | (z,uu____14477)
                                                                 ->
                                                                 let uu____14478
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14478)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14462
                                                       in
                                                    uu____14457
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14482 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14482
                                                    then
                                                      let uu____14483 =
                                                        let uu____14486 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14487 =
                                                          let uu____14490 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14491 =
                                                            let uu____14494 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14495 =
                                                              let uu____14498
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14503
                                                                =
                                                                let uu____14506
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14511
                                                                  =
                                                                  let uu____14514
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14514]
                                                                   in
                                                                uu____14506
                                                                  ::
                                                                  uu____14511
                                                                 in
                                                              uu____14498 ::
                                                                uu____14503
                                                               in
                                                            uu____14494 ::
                                                              uu____14495
                                                             in
                                                          uu____14490 ::
                                                            uu____14491
                                                           in
                                                        uu____14486 ::
                                                          uu____14487
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14483
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14520 =
                                                          let uu____14525 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14525)
                                                           in
                                                        TERM uu____14520  in
                                                      let uu____14526 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14526
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14531 =
                                                             let uu____14536
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
                                                               uu____14536)
                                                              in
                                                           TERM uu____14531
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14537 =
                                                      let uu____14538 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14538
                                                       in
                                                    solve env uu____14537)))))))
                   | uu____14539 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____14607 = head_matches_delta env1 wl1 t1 t2  in
           match uu____14607 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____14638,uu____14639) ->
                    let rec may_relate head3 =
                      let uu____14666 =
                        let uu____14667 = FStar_Syntax_Subst.compress head3
                           in
                        uu____14667.FStar_Syntax_Syntax.n  in
                      match uu____14666 with
                      | FStar_Syntax_Syntax.Tm_name uu____14670 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____14671 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14694;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____14695;
                            FStar_Syntax_Syntax.fv_qual = uu____14696;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14699;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____14700;
                            FStar_Syntax_Syntax.fv_qual = uu____14701;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____14705,uu____14706) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____14748) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____14754) ->
                          may_relate t
                      | uu____14759 -> false  in
                    let uu____14760 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____14760
                    then
                      let uu____14761 =
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
                                 let uu____14793 =
                                   let uu____14794 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____14794 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____14793
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____14799 = has_type_guard t1 t2  in
                             (uu____14799, wl1)
                           else
                             (let uu____14805 = has_type_guard t2 t1  in
                              (uu____14805, wl1)))
                         in
                      (match uu____14761 with
                       | (guard,wl2) ->
                           let uu____14812 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____14812)
                    else
                      (let uu____14814 =
                         let uu____14815 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14816 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____14815 uu____14816
                          in
                       giveup env1 uu____14814 orig)
                | (uu____14817,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___187_14831 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___187_14831.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___187_14831.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___187_14831.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___187_14831.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___187_14831.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___187_14831.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___187_14831.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___187_14831.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____14832,FStar_Pervasives_Native.None ) ->
                    ((let uu____14844 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14844
                      then
                        let uu____14845 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____14846 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____14847 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____14848 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____14845 uu____14846 uu____14847 uu____14848
                      else ());
                     (let uu____14850 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____14850 with
                      | (head11,args1) ->
                          let uu____14887 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____14887 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____14941 =
                                   let uu____14942 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____14943 = args_to_string args1  in
                                   let uu____14944 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____14945 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____14942 uu____14943 uu____14944
                                     uu____14945
                                    in
                                 giveup env1 uu____14941 orig
                               else
                                 (let uu____14947 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____14954 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____14954 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____14947
                                  then
                                    let uu____14955 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____14955 with
                                    | USolved wl2 ->
                                        let uu____14957 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____14957
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____14961 =
                                       base_and_refinement env1 t1  in
                                     match uu____14961 with
                                     | (base1,refinement1) ->
                                         let uu____14986 =
                                           base_and_refinement env1 t2  in
                                         (match uu____14986 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____15043 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____15043 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____15047 =
                                                          FStar_List.fold_right2
                                                            (fun uu____15080 
                                                               ->
                                                               fun
                                                                 uu____15081 
                                                                 ->
                                                                 fun
                                                                   uu____15082
                                                                    ->
                                                                   match 
                                                                    (uu____15080,
                                                                    uu____15081,
                                                                    uu____15082)
                                                                   with
                                                                   | 
                                                                   ((a,uu____15118),
                                                                    (a',uu____15120),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____15141
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____15141
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
                                                        (match uu____15047
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____15169
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____15169
                                                               then
                                                                 let uu____15170
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____15170
                                                               else ());
                                                              (let formula =
                                                                 let uu____15175
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____15175
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
                                               | uu____15183 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___188_15223 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___188_15223.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15226 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15226
          then
            let uu____15227 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15227
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15232 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15232
              then
                let uu____15233 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15234 =
                  let uu____15235 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15236 =
                    let uu____15237 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15237  in
                  Prims.strcat uu____15235 uu____15236  in
                let uu____15238 =
                  let uu____15239 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15240 =
                    let uu____15241 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15241  in
                  Prims.strcat uu____15239 uu____15240  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15233
                  uu____15234 uu____15238
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15244,uu____15245) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15270,FStar_Syntax_Syntax.Tm_delayed uu____15271) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15296,uu____15297) ->
                  let uu____15324 =
                    let uu___189_15325 = problem  in
                    let uu____15326 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___189_15325.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15326;
                      FStar_TypeChecker_Common.relation =
                        (uu___189_15325.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___189_15325.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___189_15325.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___189_15325.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___189_15325.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___189_15325.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___189_15325.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___189_15325.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15324 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15327,uu____15328) ->
                  let uu____15335 =
                    let uu___190_15336 = problem  in
                    let uu____15337 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___190_15336.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15337;
                      FStar_TypeChecker_Common.relation =
                        (uu___190_15336.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___190_15336.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___190_15336.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___190_15336.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___190_15336.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___190_15336.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___190_15336.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___190_15336.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15335 wl
              | (uu____15338,FStar_Syntax_Syntax.Tm_ascribed uu____15339) ->
                  let uu____15366 =
                    let uu___191_15367 = problem  in
                    let uu____15368 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___191_15367.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___191_15367.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___191_15367.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15368;
                      FStar_TypeChecker_Common.element =
                        (uu___191_15367.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___191_15367.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___191_15367.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___191_15367.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___191_15367.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___191_15367.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15366 wl
              | (uu____15369,FStar_Syntax_Syntax.Tm_meta uu____15370) ->
                  let uu____15377 =
                    let uu___192_15378 = problem  in
                    let uu____15379 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___192_15378.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___192_15378.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___192_15378.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15379;
                      FStar_TypeChecker_Common.element =
                        (uu___192_15378.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___192_15378.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___192_15378.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___192_15378.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___192_15378.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___192_15378.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15377 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15381),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15383)) ->
                  let uu____15392 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15392
              | (FStar_Syntax_Syntax.Tm_bvar uu____15393,uu____15394) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15395,FStar_Syntax_Syntax.Tm_bvar uu____15396) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___146_15455 =
                    match uu___146_15455 with
                    | [] -> c
                    | bs ->
                        let uu____15477 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15477
                     in
                  let uu____15486 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15486 with
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
                                    let uu____15609 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15609
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
                  let mk_t t l uu___147_15684 =
                    match uu___147_15684 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15718 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15718 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____15837 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____15838 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____15837
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____15838 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____15839,uu____15840) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15867 -> true
                    | uu____15884 -> false  in
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
                      (let uu____15925 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___193_15933 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___193_15933.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___193_15933.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___193_15933.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___193_15933.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___193_15933.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___193_15933.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___193_15933.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___193_15933.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___193_15933.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___193_15933.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___193_15933.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___193_15933.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___193_15933.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___193_15933.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___193_15933.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___193_15933.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___193_15933.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___193_15933.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___193_15933.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___193_15933.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___193_15933.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___193_15933.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___193_15933.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___193_15933.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___193_15933.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___193_15933.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___193_15933.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___193_15933.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___193_15933.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___193_15933.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___193_15933.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___193_15933.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___193_15933.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___193_15933.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___193_15933.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15925 with
                       | (uu____15936,ty,uu____15938) ->
                           let uu____15939 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15939)
                     in
                  let uu____15940 =
                    let uu____15953 = maybe_eta t1  in
                    let uu____15958 = maybe_eta t2  in
                    (uu____15953, uu____15958)  in
                  (match uu____15940 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___194_15982 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___194_15982.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___194_15982.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___194_15982.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___194_15982.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___194_15982.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___194_15982.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___194_15982.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___194_15982.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15993 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15993
                       then
                         let uu____15994 = destruct_flex_t not_abs wl  in
                         (match uu____15994 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16009 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16009.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16009.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16009.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16009.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16009.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16009.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16009.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16009.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16021 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16021
                       then
                         let uu____16022 = destruct_flex_t not_abs wl  in
                         (match uu____16022 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16037 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16037.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16037.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16037.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16037.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16037.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16037.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16037.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16037.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16039 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16052,FStar_Syntax_Syntax.Tm_abs uu____16053) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16080 -> true
                    | uu____16097 -> false  in
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
                      (let uu____16138 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___193_16146 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___193_16146.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___193_16146.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___193_16146.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___193_16146.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___193_16146.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___193_16146.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___193_16146.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___193_16146.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___193_16146.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___193_16146.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___193_16146.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___193_16146.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___193_16146.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___193_16146.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___193_16146.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___193_16146.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___193_16146.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___193_16146.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___193_16146.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___193_16146.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___193_16146.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___193_16146.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___193_16146.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___193_16146.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___193_16146.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___193_16146.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___193_16146.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___193_16146.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___193_16146.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___193_16146.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___193_16146.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___193_16146.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___193_16146.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___193_16146.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___193_16146.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16138 with
                       | (uu____16149,ty,uu____16151) ->
                           let uu____16152 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16152)
                     in
                  let uu____16153 =
                    let uu____16166 = maybe_eta t1  in
                    let uu____16171 = maybe_eta t2  in
                    (uu____16166, uu____16171)  in
                  (match uu____16153 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___194_16195 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___194_16195.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___194_16195.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___194_16195.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___194_16195.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___194_16195.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___194_16195.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___194_16195.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___194_16195.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16206 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16206
                       then
                         let uu____16207 = destruct_flex_t not_abs wl  in
                         (match uu____16207 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16222 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16222.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16222.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16222.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16222.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16222.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16222.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16222.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16222.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16234 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16234
                       then
                         let uu____16235 = destruct_flex_t not_abs wl  in
                         (match uu____16235 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16250 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16250.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16250.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16250.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16250.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16250.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16250.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16250.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16250.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16252 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16280 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16280) &&
                       (let uu____16284 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16284))
                      &&
                      (let uu____16291 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16291 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___148_16303 =
                             match uu___148_16303 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16304 -> true
                             | uu____16305 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16306 -> false)
                     in
                  let uu____16307 = as_refinement should_delta env wl t1  in
                  (match uu____16307 with
                   | (x11,phi1) ->
                       let uu____16314 = as_refinement should_delta env wl t2
                          in
                       (match uu____16314 with
                        | (x21,phi21) ->
                            let uu____16321 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16321 with
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
                                   let uu____16387 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16387
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16399 =
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
                                   let uu____16410 =
                                     let uu____16415 =
                                       let uu____16422 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16422]  in
                                     mk_t_problem wl1 uu____16415 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16410 with
                                    | (ref_prob,wl2) ->
                                        let uu____16437 =
                                          solve env1
                                            (let uu___196_16439 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___196_16439.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___196_16439.smt_ok);
                                               tcenv = (uu___196_16439.tcenv);
                                               wl_implicits =
                                                 (uu___196_16439.wl_implicits)
                                             })
                                           in
                                        (match uu____16437 with
                                         | Failed (prob,msg) ->
                                             let uu____16448 =
                                               ((let uu____16451 =
                                                   FStar_Syntax_Free.uvars
                                                     phi11
                                                    in
                                                 FStar_Util.set_is_empty
                                                   uu____16451)
                                                  &&
                                                  (let uu____16455 =
                                                     FStar_Syntax_Free.uvars
                                                       phi22
                                                      in
                                                   FStar_Util.set_is_empty
                                                     uu____16455))
                                                 && wl2.smt_ok
                                                in
                                             if uu____16448
                                             then fallback ()
                                             else giveup env1 msg prob
                                         | Success uu____16459 ->
                                             let guard =
                                               let uu____16467 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16467
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___197_16476 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___197_16476.attempting);
                                                 wl_deferred =
                                                   (uu___197_16476.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___197_16476.defer_ok);
                                                 smt_ok =
                                                   (uu___197_16476.smt_ok);
                                                 tcenv =
                                                   (uu___197_16476.tcenv);
                                                 wl_implicits =
                                                   (uu___197_16476.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16478,FStar_Syntax_Syntax.Tm_uvar uu____16479) ->
                  let uu____16508 = destruct_flex_t t1 wl  in
                  (match uu____16508 with
                   | (f1,wl1) ->
                       let uu____16515 = destruct_flex_t t2 wl1  in
                       (match uu____16515 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16522;
                    FStar_Syntax_Syntax.pos = uu____16523;
                    FStar_Syntax_Syntax.vars = uu____16524;_},uu____16525),FStar_Syntax_Syntax.Tm_uvar
                 uu____16526) ->
                  let uu____16575 = destruct_flex_t t1 wl  in
                  (match uu____16575 with
                   | (f1,wl1) ->
                       let uu____16582 = destruct_flex_t t2 wl1  in
                       (match uu____16582 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16589,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16590;
                    FStar_Syntax_Syntax.pos = uu____16591;
                    FStar_Syntax_Syntax.vars = uu____16592;_},uu____16593))
                  ->
                  let uu____16642 = destruct_flex_t t1 wl  in
                  (match uu____16642 with
                   | (f1,wl1) ->
                       let uu____16649 = destruct_flex_t t2 wl1  in
                       (match uu____16649 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16656;
                    FStar_Syntax_Syntax.pos = uu____16657;
                    FStar_Syntax_Syntax.vars = uu____16658;_},uu____16659),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16660;
                    FStar_Syntax_Syntax.pos = uu____16661;
                    FStar_Syntax_Syntax.vars = uu____16662;_},uu____16663))
                  ->
                  let uu____16732 = destruct_flex_t t1 wl  in
                  (match uu____16732 with
                   | (f1,wl1) ->
                       let uu____16739 = destruct_flex_t t2 wl1  in
                       (match uu____16739 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16746,uu____16747) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16762 = destruct_flex_t t1 wl  in
                  (match uu____16762 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16769;
                    FStar_Syntax_Syntax.pos = uu____16770;
                    FStar_Syntax_Syntax.vars = uu____16771;_},uu____16772),uu____16773)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16808 = destruct_flex_t t1 wl  in
                  (match uu____16808 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____16815,FStar_Syntax_Syntax.Tm_uvar uu____16816) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____16831,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16832;
                    FStar_Syntax_Syntax.pos = uu____16833;
                    FStar_Syntax_Syntax.vars = uu____16834;_},uu____16835))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16870,FStar_Syntax_Syntax.Tm_arrow uu____16871) ->
                  solve_t' env
                    (let uu___198_16899 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16899.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16899.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___198_16899.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___198_16899.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16899.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___198_16899.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16899.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16899.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16899.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16900;
                    FStar_Syntax_Syntax.pos = uu____16901;
                    FStar_Syntax_Syntax.vars = uu____16902;_},uu____16903),FStar_Syntax_Syntax.Tm_arrow
                 uu____16904) ->
                  solve_t' env
                    (let uu___198_16952 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16952.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16952.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___198_16952.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___198_16952.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16952.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___198_16952.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16952.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16952.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16952.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____16953,FStar_Syntax_Syntax.Tm_uvar uu____16954) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____16969,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16970;
                    FStar_Syntax_Syntax.pos = uu____16971;
                    FStar_Syntax_Syntax.vars = uu____16972;_},uu____16973))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____17008,uu____17009) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17024;
                    FStar_Syntax_Syntax.pos = uu____17025;
                    FStar_Syntax_Syntax.vars = uu____17026;_},uu____17027),uu____17028)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17063,uu____17064) ->
                  let t21 =
                    let uu____17072 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17072  in
                  solve_t env
                    (let uu___199_17098 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___199_17098.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___199_17098.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___199_17098.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___199_17098.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___199_17098.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___199_17098.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___199_17098.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___199_17098.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___199_17098.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17099,FStar_Syntax_Syntax.Tm_refine uu____17100) ->
                  let t11 =
                    let uu____17108 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17108  in
                  solve_t env
                    (let uu___200_17134 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___200_17134.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___200_17134.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___200_17134.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___200_17134.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___200_17134.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___200_17134.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___200_17134.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___200_17134.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___200_17134.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____17211 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____17211 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____17432 = br1  in
                             (match uu____17432 with
                              | (p1,w1,uu____17457) ->
                                  let uu____17474 = br2  in
                                  (match uu____17474 with
                                   | (p2,w2,uu____17493) ->
                                       let uu____17498 =
                                         let uu____17499 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____17499  in
                                       if uu____17498
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____17515 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____17515 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____17548 = br2  in
                                              (match uu____17548 with
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
                                                     let uu____17583 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____17583
                                                      in
                                                   let uu____17594 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____17617,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____17634) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____17677 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____17677
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____17594
                                                     (fun uu____17719  ->
                                                        match uu____17719
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____17740 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____17740
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____17755
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____17755
                                                                   (fun
                                                                    uu____17779
                                                                     ->
                                                                    match uu____17779
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
                         | uu____17864 -> FStar_Pervasives_Native.None  in
                       let uu____17901 = solve_branches wl1 brs1 brs2  in
                       (match uu____17901 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____17932,uu____17933) ->
                  let head1 =
                    let uu____17957 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17957
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17997 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17997
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18037 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18037
                    then
                      let uu____18038 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18039 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18040 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18038 uu____18039 uu____18040
                    else ());
                   (let uu____18042 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18042
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18049 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18049
                       then
                         let uu____18050 =
                           let uu____18057 =
                             let uu____18058 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18058 = FStar_Syntax_Util.Equal  in
                           if uu____18057
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18068 = mk_eq2 wl orig t1 t2  in
                              match uu____18068 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18050 with
                         | (guard,wl1) ->
                             let uu____18089 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18089
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18092,uu____18093) ->
                  let head1 =
                    let uu____18101 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18101
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18141 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18141
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18181 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18181
                    then
                      let uu____18182 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18183 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18184 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18182 uu____18183 uu____18184
                    else ());
                   (let uu____18186 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18186
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18193 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18193
                       then
                         let uu____18194 =
                           let uu____18201 =
                             let uu____18202 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18202 = FStar_Syntax_Util.Equal  in
                           if uu____18201
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18212 = mk_eq2 wl orig t1 t2  in
                              match uu____18212 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18194 with
                         | (guard,wl1) ->
                             let uu____18233 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18233
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18236,uu____18237) ->
                  let head1 =
                    let uu____18239 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18239
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18279 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18279
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18319 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18319
                    then
                      let uu____18320 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18321 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18322 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18320 uu____18321 uu____18322
                    else ());
                   (let uu____18324 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18324
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18331 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18331
                       then
                         let uu____18332 =
                           let uu____18339 =
                             let uu____18340 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18340 = FStar_Syntax_Util.Equal  in
                           if uu____18339
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18350 = mk_eq2 wl orig t1 t2  in
                              match uu____18350 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18332 with
                         | (guard,wl1) ->
                             let uu____18371 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18371
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18374,uu____18375) ->
                  let head1 =
                    let uu____18377 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18377
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18417 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18417
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18457 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18457
                    then
                      let uu____18458 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18459 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18460 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18458 uu____18459 uu____18460
                    else ());
                   (let uu____18462 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18462
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18469 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18469
                       then
                         let uu____18470 =
                           let uu____18477 =
                             let uu____18478 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18478 = FStar_Syntax_Util.Equal  in
                           if uu____18477
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18488 = mk_eq2 wl orig t1 t2  in
                              match uu____18488 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18470 with
                         | (guard,wl1) ->
                             let uu____18509 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18509
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18512,uu____18513) ->
                  let head1 =
                    let uu____18515 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18515
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18555 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18555
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18595 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18595
                    then
                      let uu____18596 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18597 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18598 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18596 uu____18597 uu____18598
                    else ());
                   (let uu____18600 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18600
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18607 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18607
                       then
                         let uu____18608 =
                           let uu____18615 =
                             let uu____18616 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18616 = FStar_Syntax_Util.Equal  in
                           if uu____18615
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18626 = mk_eq2 wl orig t1 t2  in
                              match uu____18626 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18608 with
                         | (guard,wl1) ->
                             let uu____18647 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18647
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____18650,uu____18651) ->
                  let head1 =
                    let uu____18667 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18667
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18707 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18707
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18747 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18747
                    then
                      let uu____18748 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18749 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18750 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18748 uu____18749 uu____18750
                    else ());
                   (let uu____18752 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18752
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18759 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18759
                       then
                         let uu____18760 =
                           let uu____18767 =
                             let uu____18768 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18768 = FStar_Syntax_Util.Equal  in
                           if uu____18767
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18778 = mk_eq2 wl orig t1 t2  in
                              match uu____18778 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18760 with
                         | (guard,wl1) ->
                             let uu____18799 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18799
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18802,FStar_Syntax_Syntax.Tm_match uu____18803) ->
                  let head1 =
                    let uu____18827 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18827
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18867 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18867
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18907 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18907
                    then
                      let uu____18908 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18909 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18910 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18908 uu____18909 uu____18910
                    else ());
                   (let uu____18912 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18912
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18919 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18919
                       then
                         let uu____18920 =
                           let uu____18927 =
                             let uu____18928 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18928 = FStar_Syntax_Util.Equal  in
                           if uu____18927
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18938 = mk_eq2 wl orig t1 t2  in
                              match uu____18938 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18920 with
                         | (guard,wl1) ->
                             let uu____18959 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18959
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18962,FStar_Syntax_Syntax.Tm_uinst uu____18963) ->
                  let head1 =
                    let uu____18971 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18971
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19011 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19011
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19051 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19051
                    then
                      let uu____19052 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19053 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19054 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19052 uu____19053 uu____19054
                    else ());
                   (let uu____19056 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19056
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19063 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19063
                       then
                         let uu____19064 =
                           let uu____19071 =
                             let uu____19072 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19072 = FStar_Syntax_Util.Equal  in
                           if uu____19071
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19082 = mk_eq2 wl orig t1 t2  in
                              match uu____19082 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19064 with
                         | (guard,wl1) ->
                             let uu____19103 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19103
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19106,FStar_Syntax_Syntax.Tm_name uu____19107) ->
                  let head1 =
                    let uu____19109 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19109
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19149 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19149
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19189 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19189
                    then
                      let uu____19190 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19191 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19192 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19190 uu____19191 uu____19192
                    else ());
                   (let uu____19194 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19194
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19201 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19201
                       then
                         let uu____19202 =
                           let uu____19209 =
                             let uu____19210 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19210 = FStar_Syntax_Util.Equal  in
                           if uu____19209
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19220 = mk_eq2 wl orig t1 t2  in
                              match uu____19220 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19202 with
                         | (guard,wl1) ->
                             let uu____19241 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19241
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19244,FStar_Syntax_Syntax.Tm_constant uu____19245) ->
                  let head1 =
                    let uu____19247 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19247
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19287 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19287
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19327 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19327
                    then
                      let uu____19328 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19329 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19330 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19328 uu____19329 uu____19330
                    else ());
                   (let uu____19332 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19332
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19339 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19339
                       then
                         let uu____19340 =
                           let uu____19347 =
                             let uu____19348 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19348 = FStar_Syntax_Util.Equal  in
                           if uu____19347
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19358 = mk_eq2 wl orig t1 t2  in
                              match uu____19358 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19340 with
                         | (guard,wl1) ->
                             let uu____19379 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19379
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19382,FStar_Syntax_Syntax.Tm_fvar uu____19383) ->
                  let head1 =
                    let uu____19385 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19385
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19425 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19425
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19465 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19465
                    then
                      let uu____19466 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19467 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19468 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19466 uu____19467 uu____19468
                    else ());
                   (let uu____19470 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19470
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19477 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19477
                       then
                         let uu____19478 =
                           let uu____19485 =
                             let uu____19486 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19486 = FStar_Syntax_Util.Equal  in
                           if uu____19485
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19496 = mk_eq2 wl orig t1 t2  in
                              match uu____19496 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19478 with
                         | (guard,wl1) ->
                             let uu____19517 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19517
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19520,FStar_Syntax_Syntax.Tm_app uu____19521) ->
                  let head1 =
                    let uu____19537 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19537
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19577 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19577
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19617 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19617
                    then
                      let uu____19618 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19619 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19620 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19618 uu____19619 uu____19620
                    else ());
                   (let uu____19622 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19622
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19629 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19629
                       then
                         let uu____19630 =
                           let uu____19637 =
                             let uu____19638 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19638 = FStar_Syntax_Util.Equal  in
                           if uu____19637
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19648 = mk_eq2 wl orig t1 t2  in
                              match uu____19648 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19630 with
                         | (guard,wl1) ->
                             let uu____19669 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19669
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____19672,FStar_Syntax_Syntax.Tm_let uu____19673) ->
                  let uu____19698 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____19698
                  then
                    let uu____19699 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____19699
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____19701,uu____19702) ->
                  let uu____19715 =
                    let uu____19720 =
                      let uu____19721 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19722 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19723 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19724 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19721 uu____19722 uu____19723 uu____19724
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19720)
                     in
                  FStar_Errors.raise_error uu____19715
                    t1.FStar_Syntax_Syntax.pos
              | (uu____19725,FStar_Syntax_Syntax.Tm_let uu____19726) ->
                  let uu____19739 =
                    let uu____19744 =
                      let uu____19745 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19746 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19747 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19748 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19745 uu____19746 uu____19747 uu____19748
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19744)
                     in
                  FStar_Errors.raise_error uu____19739
                    t1.FStar_Syntax_Syntax.pos
              | uu____19749 -> giveup env "head tag mismatch" orig))))

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
          (let uu____19808 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____19808
           then
             let uu____19809 =
               let uu____19810 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____19810  in
             let uu____19811 =
               let uu____19812 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____19812  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____19809 uu____19811
           else ());
          (let uu____19814 =
             let uu____19815 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____19815  in
           if uu____19814
           then
             let uu____19816 =
               let uu____19817 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____19818 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____19817 uu____19818
                in
             giveup env uu____19816 orig
           else
             (let uu____19820 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____19820 with
              | (ret_sub_prob,wl1) ->
                  let uu____19827 =
                    FStar_List.fold_right2
                      (fun uu____19860  ->
                         fun uu____19861  ->
                           fun uu____19862  ->
                             match (uu____19860, uu____19861, uu____19862)
                             with
                             | ((a1,uu____19898),(a2,uu____19900),(arg_sub_probs,wl2))
                                 ->
                                 let uu____19921 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____19921 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____19827 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____19950 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____19950  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____19980 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____19983)::[] -> wp1
              | uu____20000 ->
                  let uu____20009 =
                    let uu____20010 =
                      let uu____20011 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20011  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20010
                     in
                  failwith uu____20009
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20017 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20017]
              | x -> x  in
            let uu____20019 =
              let uu____20028 =
                let uu____20035 =
                  let uu____20036 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20036 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20035  in
              [uu____20028]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20019;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20049 = lift_c1 ()  in solve_eq uu____20049 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___149_20055  ->
                       match uu___149_20055 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20056 -> false))
                in
             let uu____20057 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20083)::uu____20084,(wp2,uu____20086)::uu____20087)
                   -> (wp1, wp2)
               | uu____20140 ->
                   let uu____20161 =
                     let uu____20166 =
                       let uu____20167 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20168 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20167 uu____20168
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20166)
                      in
                   FStar_Errors.raise_error uu____20161
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20057 with
             | (wpc1,wpc2) ->
                 let uu____20175 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20175
                 then
                   let uu____20178 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20178 wl
                 else
                   (let uu____20180 =
                      let uu____20187 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20187  in
                    match uu____20180 with
                    | (c2_decl,qualifiers) ->
                        let uu____20208 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20208
                        then
                          let c1_repr =
                            let uu____20212 =
                              let uu____20213 =
                                let uu____20214 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20214  in
                              let uu____20215 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20213 uu____20215
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20212
                             in
                          let c2_repr =
                            let uu____20217 =
                              let uu____20218 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20219 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20218 uu____20219
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20217
                             in
                          let uu____20220 =
                            let uu____20225 =
                              let uu____20226 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20227 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20226 uu____20227
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20225
                             in
                          (match uu____20220 with
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
                                 ((let uu____20241 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20241
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20244 =
                                     let uu____20251 =
                                       let uu____20252 =
                                         let uu____20267 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20270 =
                                           let uu____20279 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20286 =
                                             let uu____20295 =
                                               let uu____20302 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20302
                                                in
                                             [uu____20295]  in
                                           uu____20279 :: uu____20286  in
                                         (uu____20267, uu____20270)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20252
                                        in
                                     FStar_Syntax_Syntax.mk uu____20251  in
                                   uu____20244 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20337 =
                                    let uu____20344 =
                                      let uu____20345 =
                                        let uu____20360 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20363 =
                                          let uu____20372 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20379 =
                                            let uu____20388 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20395 =
                                              let uu____20404 =
                                                let uu____20411 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20411
                                                 in
                                              [uu____20404]  in
                                            uu____20388 :: uu____20395  in
                                          uu____20372 :: uu____20379  in
                                        (uu____20360, uu____20363)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20345
                                       in
                                    FStar_Syntax_Syntax.mk uu____20344  in
                                  uu____20337 FStar_Pervasives_Native.None r)
                              in
                           let uu____20449 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20449 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20457 =
                                   let uu____20460 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____20460
                                    in
                                 solve_prob orig uu____20457 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____20467 = FStar_Util.physical_equality c1 c2  in
        if uu____20467
        then
          let uu____20468 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20468
        else
          ((let uu____20471 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20471
            then
              let uu____20472 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20473 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20472
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20473
            else ());
           (let uu____20475 =
              let uu____20484 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20487 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20484, uu____20487)  in
            match uu____20475 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20505),FStar_Syntax_Syntax.Total
                    (t2,uu____20507)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20524 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20524 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20525,FStar_Syntax_Syntax.Total uu____20526) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20544),FStar_Syntax_Syntax.Total
                    (t2,uu____20546)) ->
                     let uu____20563 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20563 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20565),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20567)) ->
                     let uu____20584 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20584 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20586),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20588)) ->
                     let uu____20605 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20605 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20606,FStar_Syntax_Syntax.Comp uu____20607) ->
                     let uu____20616 =
                       let uu___201_20619 = problem  in
                       let uu____20622 =
                         let uu____20623 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20623
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20619.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20622;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20619.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_20619.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_20619.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20619.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20619.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20619.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20619.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20619.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20616 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20624,FStar_Syntax_Syntax.Comp uu____20625) ->
                     let uu____20634 =
                       let uu___201_20637 = problem  in
                       let uu____20640 =
                         let uu____20641 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20641
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20637.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20640;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20637.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_20637.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_20637.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20637.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20637.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20637.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20637.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20637.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20634 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20642,FStar_Syntax_Syntax.GTotal uu____20643) ->
                     let uu____20652 =
                       let uu___202_20655 = problem  in
                       let uu____20658 =
                         let uu____20659 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20659
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20655.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_20655.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20655.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20658;
                         FStar_TypeChecker_Common.element =
                           (uu___202_20655.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20655.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20655.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20655.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20655.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20655.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20652 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20660,FStar_Syntax_Syntax.Total uu____20661) ->
                     let uu____20670 =
                       let uu___202_20673 = problem  in
                       let uu____20676 =
                         let uu____20677 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20677
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20673.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_20673.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20673.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20676;
                         FStar_TypeChecker_Common.element =
                           (uu___202_20673.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20673.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20673.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20673.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20673.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20673.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20670 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20678,FStar_Syntax_Syntax.Comp uu____20679) ->
                     let uu____20680 =
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
                     if uu____20680
                     then
                       let uu____20681 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____20681 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20685 =
                            let uu____20690 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____20690
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20696 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____20697 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____20696, uu____20697))
                             in
                          match uu____20685 with
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
                           (let uu____20704 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____20704
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20706 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____20706 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20709 =
                                  let uu____20710 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____20711 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____20710 uu____20711
                                   in
                                giveup env uu____20709 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____20718 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20746  ->
              match uu____20746 with
              | (uu____20755,tm,uu____20757,uu____20758) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____20718 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____20791 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____20791 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____20809 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____20837  ->
                match uu____20837 with
                | (u1,u2) ->
                    let uu____20844 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____20845 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____20844 uu____20845))
         in
      FStar_All.pipe_right uu____20809 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____20872,[])) -> "{}"
      | uu____20897 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____20920 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____20920
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____20923 =
              FStar_List.map
                (fun uu____20933  ->
                   match uu____20933 with
                   | (uu____20938,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____20923 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____20943 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____20943 imps
  
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
                  let uu____20996 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____20996
                  then
                    let uu____20997 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____20998 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____20997
                      (rel_to_string rel) uu____20998
                  else "TOP"  in
                let uu____21000 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21000 with
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
              let uu____21057 =
                let uu____21060 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____21060
                 in
              FStar_Syntax_Syntax.new_bv uu____21057 t1  in
            let uu____21063 =
              let uu____21068 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21068
               in
            match uu____21063 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____21124 = FStar_Options.eager_inference ()  in
          if uu____21124
          then
            let uu___203_21125 = probs  in
            {
              attempting = (uu___203_21125.attempting);
              wl_deferred = (uu___203_21125.wl_deferred);
              ctr = (uu___203_21125.ctr);
              defer_ok = false;
              smt_ok = (uu___203_21125.smt_ok);
              tcenv = (uu___203_21125.tcenv);
              wl_implicits = (uu___203_21125.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21145 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21145
              then
                let uu____21146 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21146
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
          ((let uu____21168 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21168
            then
              let uu____21169 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21169
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21173 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21173
             then
               let uu____21174 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21174
             else ());
            (let f2 =
               let uu____21177 =
                 let uu____21178 = FStar_Syntax_Util.unmeta f1  in
                 uu____21178.FStar_Syntax_Syntax.n  in
               match uu____21177 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21182 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___204_21183 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___204_21183.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___204_21183.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___204_21183.FStar_TypeChecker_Env.implicits)
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
            let uu____21285 =
              let uu____21286 =
                let uu____21287 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21287;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21286  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____21285
  
let with_guard_no_simp :
  'Auu____21302 .
    'Auu____21302 ->
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
            let uu____21325 =
              let uu____21326 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21326;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21325
  
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
          (let uu____21364 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21364
           then
             let uu____21365 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21366 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21365
               uu____21366
           else ());
          (let uu____21368 =
             let uu____21373 = empty_worklist env  in
             let uu____21374 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____21373 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____21374
              in
           match uu____21368 with
           | (prob,wl) ->
               let g =
                 let uu____21382 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21400  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21382  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21442 = try_teq true env t1 t2  in
        match uu____21442 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21446 = FStar_TypeChecker_Env.get_range env  in
              let uu____21447 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21446 uu____21447);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21454 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21454
              then
                let uu____21455 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21456 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21457 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21455
                  uu____21456 uu____21457
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
          let uu____21479 = FStar_TypeChecker_Env.get_range env  in
          let uu____21480 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21479 uu____21480
  
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
        (let uu____21505 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21505
         then
           let uu____21506 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21507 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21506 uu____21507
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21510 =
           let uu____21517 = empty_worklist env  in
           let uu____21518 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____21517 env c1 rel c2 FStar_Pervasives_Native.None
             uu____21518 "sub_comp"
            in
         match uu____21510 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21528 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21546  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21528)
  
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
      fun uu____21599  ->
        match uu____21599 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21642 =
                 let uu____21647 =
                   let uu____21648 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21649 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21648 uu____21649
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21647)  in
               let uu____21650 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21642 uu____21650)
               in
            let equiv1 v1 v' =
              let uu____21662 =
                let uu____21667 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21668 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21667, uu____21668)  in
              match uu____21662 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21687 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21717 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____21717 with
                      | FStar_Syntax_Syntax.U_unif uu____21724 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21753  ->
                                    match uu____21753 with
                                    | (u,v') ->
                                        let uu____21762 = equiv1 v1 v'  in
                                        if uu____21762
                                        then
                                          let uu____21765 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____21765 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____21781 -> []))
               in
            let uu____21786 =
              let wl =
                let uu___205_21790 = empty_worklist env  in
                {
                  attempting = (uu___205_21790.attempting);
                  wl_deferred = (uu___205_21790.wl_deferred);
                  ctr = (uu___205_21790.ctr);
                  defer_ok = false;
                  smt_ok = (uu___205_21790.smt_ok);
                  tcenv = (uu___205_21790.tcenv);
                  wl_implicits = (uu___205_21790.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21808  ->
                      match uu____21808 with
                      | (lb,v1) ->
                          let uu____21815 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____21815 with
                           | USolved wl1 -> ()
                           | uu____21817 -> fail1 lb v1)))
               in
            let rec check_ineq uu____21827 =
              match uu____21827 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21836) -> true
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
                      uu____21859,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21861,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21872) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21879,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21887 -> false)
               in
            let uu____21892 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21907  ->
                      match uu____21907 with
                      | (u,v1) ->
                          let uu____21914 = check_ineq (u, v1)  in
                          if uu____21914
                          then true
                          else
                            ((let uu____21917 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____21917
                              then
                                let uu____21918 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____21919 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____21918
                                  uu____21919
                              else ());
                             false)))
               in
            if uu____21892
            then ()
            else
              ((let uu____21923 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____21923
                then
                  ((let uu____21925 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21925);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21935 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21935))
                else ());
               (let uu____21945 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____21945))
  
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
        let fail1 uu____22012 =
          match uu____22012 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___206_22033 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___206_22033.attempting);
            wl_deferred = (uu___206_22033.wl_deferred);
            ctr = (uu___206_22033.ctr);
            defer_ok;
            smt_ok = (uu___206_22033.smt_ok);
            tcenv = (uu___206_22033.tcenv);
            wl_implicits = (uu___206_22033.wl_implicits)
          }  in
        (let uu____22035 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22035
         then
           let uu____22036 = FStar_Util.string_of_bool defer_ok  in
           let uu____22037 = wl_to_string wl  in
           let uu____22038 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22036 uu____22037 uu____22038
         else ());
        (let g1 =
           let uu____22049 = solve_and_commit env wl fail1  in
           match uu____22049 with
           | FStar_Pervasives_Native.Some
               (uu____22056::uu____22057,uu____22058) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___207_22083 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___207_22083.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___207_22083.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22092 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___208_22100 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___208_22100.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___208_22100.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___208_22100.FStar_TypeChecker_Env.implicits)
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
    let uu____22148 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22148 with
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
            let uu___209_22271 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___209_22271.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___209_22271.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___209_22271.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22272 =
            let uu____22273 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22273  in
          if uu____22272
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22281 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22282 =
                       let uu____22283 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22283
                        in
                     FStar_Errors.diag uu____22281 uu____22282)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22287 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22288 =
                        let uu____22289 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22289
                         in
                      FStar_Errors.diag uu____22287 uu____22288)
                   else ();
                   (let uu____22292 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22292 "discharge_guard'"
                      env vc1);
                   (let uu____22293 = check_trivial vc1  in
                    match uu____22293 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22300 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22301 =
                                let uu____22302 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22302
                                 in
                              FStar_Errors.diag uu____22300 uu____22301)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22307 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22308 =
                                let uu____22309 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22309
                                 in
                              FStar_Errors.diag uu____22307 uu____22308)
                           else ();
                           (let vcs =
                              let uu____22322 = FStar_Options.use_tactics ()
                                 in
                              if uu____22322
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22344  ->
                                     (let uu____22346 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____22346);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22389  ->
                                              match uu____22389 with
                                              | (env1,goal,opts) ->
                                                  let uu____22405 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22405, opts)))))
                              else
                                (let uu____22407 =
                                   let uu____22414 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22414)  in
                                 [uu____22407])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22451  ->
                                    match uu____22451 with
                                    | (env1,goal,opts) ->
                                        let uu____22467 = check_trivial goal
                                           in
                                        (match uu____22467 with
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
                                                (let uu____22475 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22476 =
                                                   let uu____22477 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22478 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22477 uu____22478
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22475 uu____22476)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22481 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22482 =
                                                   let uu____22483 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22483
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22481 uu____22482)
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
      let uu____22497 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22497 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22504 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22504
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22515 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22515 with
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
            let uu____22548 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____22548 with
            | FStar_Pervasives_Native.Some uu____22551 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____22571 = acc  in
            match uu____22571 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22623 = hd1  in
                     (match uu____22623 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____22637 = unresolved ctx_u  in
                             if uu____22637
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___210_22649 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___210_22649.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___210_22649.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___210_22649.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___210_22649.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___210_22649.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___210_22649.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___210_22649.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___210_22649.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___210_22649.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___210_22649.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___210_22649.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___210_22649.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___210_22649.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___210_22649.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___210_22649.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___210_22649.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___210_22649.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___210_22649.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___210_22649.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___210_22649.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___210_22649.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___210_22649.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___210_22649.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___210_22649.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___210_22649.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___210_22649.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___210_22649.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___210_22649.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___210_22649.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___210_22649.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___210_22649.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___210_22649.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___210_22649.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___210_22649.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___210_22649.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___210_22649.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___210_22649.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___211_22652 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___211_22652.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___211_22652.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___211_22652.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___211_22652.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___211_22652.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___211_22652.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___211_22652.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___211_22652.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___211_22652.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___211_22652.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___211_22652.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___211_22652.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___211_22652.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___211_22652.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___211_22652.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___211_22652.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___211_22652.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___211_22652.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___211_22652.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___211_22652.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___211_22652.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___211_22652.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___211_22652.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___211_22652.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___211_22652.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___211_22652.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___211_22652.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___211_22652.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___211_22652.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___211_22652.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___211_22652.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___211_22652.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___211_22652.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___211_22652.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___211_22652.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___211_22652.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___211_22652.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____22655 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22655
                                   then
                                     let uu____22656 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____22657 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____22658 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____22659 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____22656 uu____22657 uu____22658
                                       reason uu____22659
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____22670 =
                                             let uu____22679 =
                                               let uu____22686 =
                                                 let uu____22687 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____22688 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 FStar_Util.format2
                                                   "Failed while checking implicit %s set to %s"
                                                   uu____22687 uu____22688
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____22686, r)
                                                in
                                             [uu____22679]  in
                                           FStar_Errors.add_errors
                                             uu____22670);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___214_22702 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___214_22702.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___214_22702.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___214_22702.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____22705 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____22715  ->
                                               let uu____22716 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____22717 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____22718 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____22716 uu____22717
                                                 reason uu____22718)) env2 g2
                                         true
                                        in
                                     match uu____22705 with
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
          let uu___215_22728 = g  in
          let uu____22729 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___215_22728.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___215_22728.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___215_22728.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____22729
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
        let uu____22779 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____22779 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22788 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____22788
      | (reason,e,ctx_u,r)::uu____22793 ->
          let uu____22812 =
            let uu____22817 =
              let uu____22818 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____22819 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____22818 uu____22819 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____22817)
             in
          FStar_Errors.raise_error uu____22812 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___216_22830 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___216_22830.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___216_22830.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___216_22830.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____22845 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22845 with
      | FStar_Pervasives_Native.Some uu____22851 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22867 = try_teq false env t1 t2  in
        match uu____22867 with
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
        (let uu____22901 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22901
         then
           let uu____22902 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____22903 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22902
             uu____22903
         else ());
        (let uu____22905 =
           let uu____22912 = empty_worklist env  in
           new_t_prob uu____22912 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____22905 with
         | (prob,x,wl) ->
             let g =
               let uu____22925 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____22943  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____22925  in
             ((let uu____22971 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____22971
               then
                 let uu____22972 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____22973 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____22974 =
                   let uu____22975 = FStar_Util.must g  in
                   guard_to_string env uu____22975  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____22972 uu____22973 uu____22974
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
        let uu____23009 = check_subtyping env t1 t2  in
        match uu____23009 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23028 =
              let uu____23029 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23029 g  in
            FStar_Pervasives_Native.Some uu____23028
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23047 = check_subtyping env t1 t2  in
        match uu____23047 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23066 =
              let uu____23067 =
                let uu____23068 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23068]  in
              close_guard env uu____23067 g  in
            FStar_Pervasives_Native.Some uu____23066
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23097 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23097
         then
           let uu____23098 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23099 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23098
             uu____23099
         else ());
        (let uu____23101 =
           let uu____23108 = empty_worklist env  in
           new_t_prob uu____23108 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23101 with
         | (prob,x,wl) ->
             let g =
               let uu____23115 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23133  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23115  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23162 =
                      let uu____23163 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23163]  in
                    close_guard env uu____23162 g1  in
                  discharge_guard_nosmt env g2))
  