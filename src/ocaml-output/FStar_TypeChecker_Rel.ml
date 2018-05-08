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
  'Auu____5993 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5993) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg,i)::args2 ->
              let hd1 = sn env arg  in
              (match hd1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6123 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6123
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6143 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6181 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____6218 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6224 -> false
  
let string_of_option :
  'Auu____6231 .
    ('Auu____6231 -> Prims.string) ->
      'Auu____6231 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___139_6246  ->
      match uu___139_6246 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6252 = f x  in Prims.strcat "Some " uu____6252
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___140_6257  ->
    match uu___140_6257 with
    | MisMatch (d1,d2) ->
        let uu____6268 =
          let uu____6269 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6270 =
            let uu____6271 =
              let uu____6272 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6272 ")"  in
            Prims.strcat ") (" uu____6271  in
          Prims.strcat uu____6269 uu____6270  in
        Prims.strcat "MisMatch (" uu____6268
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___141_6277  ->
    match uu___141_6277 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____6292 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____6322 = m2 ()  in
          (match uu____6322 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____6337 -> HeadMatch)
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
          let uu____6351 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6351 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6362 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6385 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6394 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6422 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6422
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6423 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6424 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6425 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6440 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6453 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6477) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6483,uu____6484) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6526) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6547;
             FStar_Syntax_Syntax.index = uu____6548;
             FStar_Syntax_Syntax.sort = t2;_},uu____6550)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6557 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6558 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6559 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6572 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6579 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6597 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6597
  
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
            let uu____6624 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6624
            then FullMatch
            else
              (let uu____6626 =
                 let uu____6635 =
                   let uu____6638 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6638  in
                 let uu____6639 =
                   let uu____6642 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6642  in
                 (uu____6635, uu____6639)  in
               MisMatch uu____6626)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6648),FStar_Syntax_Syntax.Tm_uinst (g,uu____6650)) ->
            let uu____6659 = head_matches env f g  in
            FStar_All.pipe_right uu____6659 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6662 = FStar_Const.eq_const c d  in
            if uu____6662
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6669),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6671)) ->
            let uu____6712 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6712
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6719),FStar_Syntax_Syntax.Tm_refine (y,uu____6721)) ->
            let uu____6730 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6730 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6732),uu____6733) ->
            let uu____6738 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6738 head_match
        | (uu____6739,FStar_Syntax_Syntax.Tm_refine (x,uu____6741)) ->
            let uu____6746 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6746 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6747,FStar_Syntax_Syntax.Tm_type
           uu____6748) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6749,FStar_Syntax_Syntax.Tm_arrow uu____6750) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6776),FStar_Syntax_Syntax.Tm_app (head',uu____6778))
            ->
            let uu____6819 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6819 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6821),uu____6822) ->
            let uu____6843 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6843 head_match
        | (uu____6844,FStar_Syntax_Syntax.Tm_app (head1,uu____6846)) ->
            let uu____6867 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6867 head_match
        | uu____6868 ->
            let uu____6873 =
              let uu____6882 = delta_depth_of_term env t11  in
              let uu____6885 = delta_depth_of_term env t21  in
              (uu____6882, uu____6885)  in
            MisMatch uu____6873
  
let head_matches_delta :
  'Auu____6902 .
    FStar_TypeChecker_Env.env ->
      'Auu____6902 ->
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
            let uu____6949 = FStar_Syntax_Util.head_and_args t  in
            match uu____6949 with
            | (head1,uu____6967) ->
                let uu____6988 =
                  let uu____6989 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6989.FStar_Syntax_Syntax.n  in
                (match uu____6988 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6995 =
                       let uu____6996 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6996 FStar_Option.isSome
                        in
                     if uu____6995
                     then
                       let uu____7015 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____7015
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____7019 -> FStar_Pervasives_Native.None)
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
              let uu____7152 =
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
              match uu____7152 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____7197 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____7197 with
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
                 uu____7229),uu____7230)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7248 =
                     let uu____7257 = maybe_inline t11  in
                     let uu____7260 = maybe_inline t21  in
                     (uu____7257, uu____7260)  in
                   match uu____7248 with
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
                (uu____7297,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____7298))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7316 =
                     let uu____7325 = maybe_inline t11  in
                     let uu____7328 = maybe_inline t21  in
                     (uu____7325, uu____7328)  in
                   match uu____7316 with
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
            | MisMatch uu____7377 -> fail1 r
            | uu____7386 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7399 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7399
           then
             let uu____7400 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7401 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7402 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7409 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7427 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7427
                    (fun uu____7461  ->
                       match uu____7461 with
                       | (t11,t21) ->
                           let uu____7468 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7469 =
                             let uu____7470 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7470  in
                           Prims.strcat uu____7468 uu____7469))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____7400
               uu____7401 uu____7402 uu____7409
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7482 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7482 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___142_7495  ->
    match uu___142_7495 with
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
      let uu___167_7532 = p  in
      let uu____7535 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7536 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___167_7532.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7535;
        FStar_TypeChecker_Common.relation =
          (uu___167_7532.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7536;
        FStar_TypeChecker_Common.element =
          (uu___167_7532.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___167_7532.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___167_7532.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___167_7532.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___167_7532.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___167_7532.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7550 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7550
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____7555 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7577 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7577 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7585 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7585 with
           | (lh,lhs_args) ->
               let uu____7626 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7626 with
                | (rh,rhs_args) ->
                    let uu____7667 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7680,FStar_Syntax_Syntax.Tm_uvar uu____7681)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7762 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7785,uu____7786)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7804 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7804.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7804.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7804.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7804.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7804.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7804.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7804.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7804.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7804.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7807,FStar_Syntax_Syntax.Tm_uvar uu____7808)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___168_7826 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_7826.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_7826.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_7826.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_7826.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_7826.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___168_7826.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_7826.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_7826.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_7826.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7829,FStar_Syntax_Syntax.Tm_arrow uu____7830)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7860 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7860.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7860.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7860.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7860.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7860.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7860.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7860.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7860.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7860.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7863,FStar_Syntax_Syntax.Tm_type uu____7864)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7882 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7882.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7882.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7882.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7882.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7882.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7882.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7882.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7882.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7882.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7885,FStar_Syntax_Syntax.Tm_uvar uu____7886)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___169_7904 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___169_7904.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___169_7904.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___169_7904.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___169_7904.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___169_7904.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___169_7904.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___169_7904.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___169_7904.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___169_7904.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7907,FStar_Syntax_Syntax.Tm_uvar uu____7908)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7925,uu____7926)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7943,FStar_Syntax_Syntax.Tm_uvar uu____7944)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7961,uu____7962) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7667 with
                     | (rank,tp1) ->
                         let uu____7975 =
                           FStar_All.pipe_right
                             (let uu___170_7979 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___170_7979.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___170_7979.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___170_7979.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___170_7979.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___170_7979.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___170_7979.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___170_7979.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___170_7979.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___170_7979.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7975))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7985 =
            FStar_All.pipe_right
              (let uu___171_7989 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___171_7989.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___171_7989.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___171_7989.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___171_7989.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___171_7989.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___171_7989.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___171_7989.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___171_7989.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___171_7989.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7985)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8050 probs =
      match uu____8050 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8131 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8152 = rank wl.tcenv hd1  in
               (match uu____8152 with
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
                      (let uu____8211 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8215 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8215)
                          in
                       if uu____8211
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
          let uu____8283 = FStar_Syntax_Util.head_and_args t  in
          match uu____8283 with
          | (hd1,uu____8299) ->
              let uu____8320 =
                let uu____8321 = FStar_Syntax_Subst.compress hd1  in
                uu____8321.FStar_Syntax_Syntax.n  in
              (match uu____8320 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8325) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8359  ->
                           match uu____8359 with
                           | (y,uu____8365) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8379  ->
                                       match uu____8379 with
                                       | (x,uu____8385) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8386 -> false)
           in
        let uu____8387 = rank tcenv p  in
        match uu____8387 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8394 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8421 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8435 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8449 -> false
  
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
                        let uu____8501 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8501 with
                        | (k,uu____8507) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8517 -> false)))
            | uu____8518 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8570 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8576 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8576 = (Prims.parse_int "0")))
                           in
                        if uu____8570 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8592 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8598 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8598 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8592)
               in
            let uu____8599 = filter1 u12  in
            let uu____8602 = filter1 u22  in (uu____8599, uu____8602)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8631 = filter_out_common_univs us1 us2  in
                (match uu____8631 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8690 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8690 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8693 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8703 =
                          let uu____8704 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8705 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8704
                            uu____8705
                           in
                        UFailed uu____8703))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8729 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8729 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8755 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8755 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8758 ->
                let uu____8763 =
                  let uu____8764 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8765 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8764
                    uu____8765 msg
                   in
                UFailed uu____8763
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8766,uu____8767) ->
              let uu____8768 =
                let uu____8769 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8770 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8769 uu____8770
                 in
              failwith uu____8768
          | (FStar_Syntax_Syntax.U_unknown ,uu____8771) ->
              let uu____8772 =
                let uu____8773 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8774 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8773 uu____8774
                 in
              failwith uu____8772
          | (uu____8775,FStar_Syntax_Syntax.U_bvar uu____8776) ->
              let uu____8777 =
                let uu____8778 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8779 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8778 uu____8779
                 in
              failwith uu____8777
          | (uu____8780,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8781 =
                let uu____8782 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8783 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8782 uu____8783
                 in
              failwith uu____8781
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8807 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8807
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8821 = occurs_univ v1 u3  in
              if uu____8821
              then
                let uu____8822 =
                  let uu____8823 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8824 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8823 uu____8824
                   in
                try_umax_components u11 u21 uu____8822
              else
                (let uu____8826 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8826)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8838 = occurs_univ v1 u3  in
              if uu____8838
              then
                let uu____8839 =
                  let uu____8840 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8841 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8840 uu____8841
                   in
                try_umax_components u11 u21 uu____8839
              else
                (let uu____8843 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8843)
          | (FStar_Syntax_Syntax.U_max uu____8844,uu____8845) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8851 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8851
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8853,FStar_Syntax_Syntax.U_max uu____8854) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8860 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8860
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8862,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8863,FStar_Syntax_Syntax.U_name
             uu____8864) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8865) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8866) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8867,FStar_Syntax_Syntax.U_succ
             uu____8868) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8869,FStar_Syntax_Syntax.U_zero
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
      let uu____8969 = bc1  in
      match uu____8969 with
      | (bs1,mk_cod1) ->
          let uu____9013 = bc2  in
          (match uu____9013 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9124 = aux xs ys  in
                     (match uu____9124 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9207 =
                       let uu____9214 = mk_cod1 xs  in ([], uu____9214)  in
                     let uu____9217 =
                       let uu____9224 = mk_cod2 ys  in ([], uu____9224)  in
                     (uu____9207, uu____9217)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____9247 'Auu____9248 'Auu____9249 .
    ('Auu____9247,'Auu____9248,'Auu____9249 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___143_9262  ->
    match uu___143_9262 with
    | (uu____9271,uu____9272,[]) -> true
    | uu____9275 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9306 = f  in
      match uu____9306 with
      | (uu____9313,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9314;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9315;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9318;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9319;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9320;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9372  ->
                 match uu____9372 with
                 | (y,uu____9378) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9500 =
                  let uu____9513 =
                    let uu____9516 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9516  in
                  ((FStar_List.rev pat_binders), uu____9513)  in
                FStar_Pervasives_Native.Some uu____9500
            | (uu____9543,[]) ->
                let uu____9566 =
                  let uu____9579 =
                    let uu____9582 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9582  in
                  ((FStar_List.rev pat_binders), uu____9579)  in
                FStar_Pervasives_Native.Some uu____9566
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9647 =
                  let uu____9648 = FStar_Syntax_Subst.compress a  in
                  uu____9648.FStar_Syntax_Syntax.n  in
                (match uu____9647 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9666 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9666
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___172_9687 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___172_9687.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___172_9687.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9691 =
                            let uu____9692 =
                              let uu____9699 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9699)  in
                            FStar_Syntax_Syntax.NT uu____9692  in
                          [uu____9691]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___173_9711 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___173_9711.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___173_9711.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9712 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9740 =
                  let uu____9753 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9753  in
                (match uu____9740 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9816 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9843 ->
               let uu____9844 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9844 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10120 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10120
       then
         let uu____10121 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10121
       else ());
      (let uu____10123 = next_prob probs  in
       match uu____10123 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___174_10150 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___174_10150.wl_deferred);
               ctr = (uu___174_10150.ctr);
               defer_ok = (uu___174_10150.defer_ok);
               smt_ok = (uu___174_10150.smt_ok);
               tcenv = (uu___174_10150.tcenv);
               wl_implicits = (uu___174_10150.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10157 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10157
                then
                  let uu____10158 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10158
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
                          (let uu___175_10163 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___175_10163.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___175_10163.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___175_10163.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___175_10163.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___175_10163.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___175_10163.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___175_10163.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___175_10163.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___175_10163.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10185 ->
                let uu____10194 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10253  ->
                          match uu____10253 with
                          | (c,uu____10261,uu____10262) -> c < probs.ctr))
                   in
                (match uu____10194 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10303 =
                            let uu____10308 =
                              FStar_List.map
                                (fun uu____10323  ->
                                   match uu____10323 with
                                   | (uu____10334,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10308, (probs.wl_implicits))  in
                          Success uu____10303
                      | uu____10337 ->
                          let uu____10346 =
                            let uu___176_10347 = probs  in
                            let uu____10348 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10367  ->
                                      match uu____10367 with
                                      | (uu____10374,uu____10375,y) -> y))
                               in
                            {
                              attempting = uu____10348;
                              wl_deferred = rest;
                              ctr = (uu___176_10347.ctr);
                              defer_ok = (uu___176_10347.defer_ok);
                              smt_ok = (uu___176_10347.smt_ok);
                              tcenv = (uu___176_10347.tcenv);
                              wl_implicits = (uu___176_10347.wl_implicits)
                            }  in
                          solve env uu____10346))))

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
            let uu____10382 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10382 with
            | USolved wl1 ->
                let uu____10384 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10384
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
                  let uu____10436 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10436 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10439 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10451;
                  FStar_Syntax_Syntax.vars = uu____10452;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10455;
                  FStar_Syntax_Syntax.vars = uu____10456;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10468,uu____10469) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10476,FStar_Syntax_Syntax.Tm_uinst uu____10477) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10484 -> USolved wl

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
            ((let uu____10494 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10494
              then
                let uu____10495 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10495 msg
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
              let uu____10580 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10580 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10632 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10632
               then
                 let uu____10633 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10634 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10633
                   uu____10634
               else ());
              (let uu____10636 = head_matches_delta env1 () t1 t2  in
               match uu____10636 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____10681 ->
                        let uu____10690 = eq_prob t1 t2 wl2  in
                        (match uu____10690 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____10737 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10752 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10753 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10752, uu____10753)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10758 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10759 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10758, uu____10759)
                           in
                        (match uu____10737 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10790 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10790 with
                               | (t1_hd,t1_args) ->
                                   let uu____10829 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10829 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____10883 =
                                             let uu____10890 =
                                               let uu____10899 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____10899 :: t1_args  in
                                             let uu____10912 =
                                               let uu____10919 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____10919 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____10960  ->
                                                  fun uu____10961  ->
                                                    fun uu____10962  ->
                                                      match (uu____10960,
                                                              uu____10961,
                                                              uu____10962)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____11004),
                                                         (a2,uu____11006)) ->
                                                          let uu____11031 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____11031
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____10890
                                               uu____10912
                                              in
                                           match uu____10883 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___177_11057 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___177_11057.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___177_11057.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11073 =
                                                 solve env1 wl'  in
                                               (match uu____11073 with
                                                | Success (uu____11076,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___178_11080 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___178_11080.attempting);
                                                           wl_deferred =
                                                             (uu___178_11080.wl_deferred);
                                                           ctr =
                                                             (uu___178_11080.ctr);
                                                           defer_ok =
                                                             (uu___178_11080.defer_ok);
                                                           smt_ok =
                                                             (uu___178_11080.smt_ok);
                                                           tcenv =
                                                             (uu___178_11080.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11089 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11121 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11121 with
                               | (t1_base,p1_opt) ->
                                   let uu____11162 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11162 with
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
                                              let uu____11293 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____11293
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
                                              let uu____11323 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11323
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
                                              let uu____11353 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11353
                                          | uu____11356 -> t_base  in
                                        let uu____11373 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11373 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11387 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11387, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11394 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11394 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11435 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11435 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11476 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11476
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
                             let uu____11500 = combine t11 t21 wl2  in
                             (match uu____11500 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11533 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11533
                                    then
                                      let uu____11534 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11534
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11573 ts1 =
              match uu____11573 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11636 = pairwise out t wl2  in
                       (match uu____11636 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11672 =
              let uu____11683 = FStar_List.hd ts  in (uu____11683, [], wl1)
               in
            let uu____11692 = FStar_List.tl ts  in
            aux uu____11672 uu____11692  in
          let uu____11699 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11699 with
          | (this_flex,this_rigid) ->
              let uu____11711 =
                let uu____11712 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11712.FStar_Syntax_Syntax.n  in
              (match uu____11711 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11733 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11733
                   then
                     let uu____11734 = destruct_flex_t this_flex wl  in
                     (match uu____11734 with
                      | (flex,wl1) ->
                          let uu____11741 = quasi_pattern env flex  in
                          (match uu____11741 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11759 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11759
                                 then
                                   let uu____11760 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11760
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
                             ((let uu___179_11765 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___179_11765.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___179_11765.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___179_11765.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___179_11765.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___179_11765.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___179_11765.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___179_11765.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___179_11765.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___179_11765.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11766 ->
                   ((let uu____11768 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11768
                     then
                       let uu____11769 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11769
                     else ());
                    (let uu____11771 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11771 with
                     | (u,_args) ->
                         let uu____11808 =
                           let uu____11809 = FStar_Syntax_Subst.compress u
                              in
                           uu____11809.FStar_Syntax_Syntax.n  in
                         (match uu____11808 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____11840 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____11840 with
                                | (u',uu____11856) ->
                                    let uu____11877 =
                                      let uu____11878 = whnf env u'  in
                                      uu____11878.FStar_Syntax_Syntax.n  in
                                    (match uu____11877 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____11903 -> false)
                                 in
                              let uu____11904 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___144_11927  ->
                                        match uu___144_11927 with
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
                                             | uu____11936 -> false)
                                        | uu____11939 -> false))
                                 in
                              (match uu____11904 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____11953 = whnf env this_rigid
                                        in
                                     let uu____11954 =
                                       FStar_List.collect
                                         (fun uu___145_11960  ->
                                            match uu___145_11960 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____11966 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____11966]
                                            | uu____11968 -> []) bounds_probs
                                        in
                                     uu____11953 :: uu____11954  in
                                   let uu____11969 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____11969 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____12000 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____12015 =
                                              let uu____12016 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____12016.FStar_Syntax_Syntax.n
                                               in
                                            match uu____12015 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____12028 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____12028)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____12037 -> bound  in
                                          let uu____12038 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____12038)  in
                                        (match uu____12000 with
                                         | (bound_typ,(eq_prob,wl')) ->
                                             ((let uu____12066 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____12066
                                               then
                                                 let wl'1 =
                                                   let uu___180_12068 = wl1
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___180_12068.wl_deferred);
                                                     ctr =
                                                       (uu___180_12068.ctr);
                                                     defer_ok =
                                                       (uu___180_12068.defer_ok);
                                                     smt_ok =
                                                       (uu___180_12068.smt_ok);
                                                     tcenv =
                                                       (uu___180_12068.tcenv);
                                                     wl_implicits =
                                                       (uu___180_12068.wl_implicits)
                                                   }  in
                                                 let uu____12069 =
                                                   wl_to_string wl'1  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____12069
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____12072 =
                                                 solve_t env eq_prob
                                                   (let uu___181_12074 = wl'
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___181_12074.wl_deferred);
                                                      ctr =
                                                        (uu___181_12074.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___181_12074.smt_ok);
                                                      tcenv =
                                                        (uu___181_12074.tcenv);
                                                      wl_implicits =
                                                        (uu___181_12074.wl_implicits)
                                                    })
                                                  in
                                               match uu____12072 with
                                               | Success uu____12075 ->
                                                   let wl2 =
                                                     let uu___182_12081 = wl'
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___182_12081.wl_deferred);
                                                       ctr =
                                                         (uu___182_12081.ctr);
                                                       defer_ok =
                                                         (uu___182_12081.defer_ok);
                                                       smt_ok =
                                                         (uu___182_12081.smt_ok);
                                                       tcenv =
                                                         (uu___182_12081.tcenv);
                                                       wl_implicits =
                                                         (uu___182_12081.wl_implicits)
                                                     }  in
                                                   let wl3 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl2
                                                      in
                                                   let uu____12085 =
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
                                                    (let uu____12097 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12097
                                                     then
                                                       let uu____12098 =
                                                         let uu____12099 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12099
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12098
                                                     else ());
                                                    (let uu____12105 =
                                                       let uu____12120 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12120)
                                                        in
                                                     match uu____12105 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12142))
                                                         ->
                                                         let uu____12167 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12167
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
                                                         let uu____12206 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12206
                                                          with
                                                          | (eq_prob1,wl2) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl2 tp x
                                                                  phi
                                                                 in
                                                              let wl3 =
                                                                let uu____12223
                                                                  =
                                                                  let uu____12228
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12228
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12223
                                                                  [] wl2
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl3))
                                                     | uu____12233 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12248 when flip ->
                              let uu____12249 =
                                let uu____12250 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12251 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12250 uu____12251
                                 in
                              failwith uu____12249
                          | uu____12252 ->
                              let uu____12253 =
                                let uu____12254 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12255 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12254 uu____12255
                                 in
                              failwith uu____12253))))

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
                      (fun uu____12283  ->
                         match uu____12283 with
                         | (x,i) ->
                             let uu____12294 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12294, i)) bs_lhs
                     in
                  let uu____12295 = lhs  in
                  match uu____12295 with
                  | (uu____12296,u_lhs,uu____12298) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12411 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12421 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12421, univ)
                             in
                          match uu____12411 with
                          | (k,univ) ->
                              let uu____12434 =
                                let uu____12441 =
                                  let uu____12444 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12444
                                   in
                                copy_uvar u_lhs uu____12441 wl2  in
                              (match uu____12434 with
                               | (uu____12457,u,wl3) ->
                                   let uu____12460 =
                                     let uu____12463 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12463
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12460, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12499 =
                              let uu____12512 =
                                let uu____12521 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12521 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12567  ->
                                   fun uu____12568  ->
                                     match (uu____12567, uu____12568) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12659 =
                                           let uu____12666 =
                                             let uu____12669 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12669
                                              in
                                           copy_uvar u_lhs uu____12666 wl2
                                            in
                                         (match uu____12659 with
                                          | (uu____12692,t_a,wl3) ->
                                              let uu____12695 =
                                                let uu____12702 =
                                                  let uu____12705 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12705
                                                   in
                                                copy_uvar u_lhs uu____12702
                                                  wl3
                                                 in
                                              (match uu____12695 with
                                               | (uu____12720,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12512
                                ([], wl1)
                               in
                            (match uu____12499 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___183_12781 = ct  in
                                   let uu____12782 =
                                     let uu____12785 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12785
                                      in
                                   let uu____12800 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___183_12781.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___183_12781.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12782;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12800;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___183_12781.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___184_12818 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___184_12818.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___184_12818.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12821 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12821 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12875 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12875 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12892 =
                                          let uu____12897 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12897)  in
                                        TERM uu____12892  in
                                      let uu____12898 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12898 with
                                       | (sub_prob,wl3) ->
                                           let uu____12909 =
                                             let uu____12910 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12910
                                              in
                                           solve env uu____12909))
                             | (x,imp)::formals2 ->
                                 let uu____12924 =
                                   let uu____12931 =
                                     let uu____12934 =
                                       let uu____12937 =
                                         let uu____12938 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____12938
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____12937
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____12934
                                      in
                                   copy_uvar u_lhs uu____12931 wl1  in
                                 (match uu____12924 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____12962 =
                                          let uu____12965 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12965
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12962 t_y
                                         in
                                      let uu____12966 =
                                        let uu____12969 =
                                          let uu____12972 =
                                            let uu____12973 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12973, imp)  in
                                          [uu____12972]  in
                                        FStar_List.append bs_terms
                                          uu____12969
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12966 formals2 wl2)
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
              (let uu____13015 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13015
               then
                 let uu____13016 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13017 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13016 (rel_to_string (p_rel orig)) uu____13017
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13122 = rhs wl1 scope env1 subst1  in
                     (match uu____13122 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13142 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13142
                            then
                              let uu____13143 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13143
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___185_13197 = hd1  in
                       let uu____13198 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___185_13197.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___185_13197.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13198
                       }  in
                     let hd21 =
                       let uu___186_13202 = hd2  in
                       let uu____13203 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___186_13202.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___186_13202.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13203
                       }  in
                     let uu____13206 =
                       let uu____13211 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13211
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13206 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13230 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13230
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13234 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13234 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13289 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13289
                                  in
                               ((let uu____13301 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13301
                                 then
                                   let uu____13302 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13303 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13302
                                     uu____13303
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13330 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13359 = aux wl [] env [] bs1 bs2  in
               match uu____13359 with
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
        (let uu____13410 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13410 wl)

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
              let uu____13424 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13424 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13454 = lhs1  in
              match uu____13454 with
              | (uu____13457,ctx_u,uu____13459) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13465 ->
                        let uu____13466 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13466 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13513 = quasi_pattern env1 lhs1  in
              match uu____13513 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13543) ->
                  let uu____13548 = lhs1  in
                  (match uu____13548 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13562 = occurs_check ctx_u rhs1  in
                       (match uu____13562 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13604 =
                                let uu____13611 =
                                  let uu____13612 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13612
                                   in
                                FStar_Util.Inl uu____13611  in
                              (uu____13604, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13632 =
                                 let uu____13633 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13633  in
                               if uu____13632
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13653 =
                                    let uu____13660 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13660  in
                                  let uu____13665 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13653, uu____13665)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13727  ->
                     match uu____13727 with
                     | (x,i) ->
                         let uu____13738 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13738, i)) bs_lhs
                 in
              let uu____13739 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13739 with
              | (rhs_hd,args) ->
                  let uu____13776 = FStar_Util.prefix args  in
                  (match uu____13776 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13834 = lhs1  in
                       (match uu____13834 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13838 =
                              let uu____13849 =
                                let uu____13856 =
                                  let uu____13859 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13859
                                   in
                                copy_uvar u_lhs uu____13856 wl1  in
                              match uu____13849 with
                              | (uu____13880,t_last_arg,wl2) ->
                                  let uu____13883 =
                                    let uu____13890 =
                                      let uu____13893 =
                                        let uu____13900 =
                                          let uu____13907 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____13907]  in
                                        FStar_List.append bs_lhs uu____13900
                                         in
                                      let uu____13924 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____13893
                                        uu____13924
                                       in
                                    copy_uvar u_lhs uu____13890 wl2  in
                                  (match uu____13883 with
                                   | (uu____13937,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13943 =
                                         let uu____13950 =
                                           let uu____13953 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____13953
                                            in
                                         copy_uvar u_lhs uu____13950 wl3  in
                                       (match uu____13943 with
                                        | (uu____13966,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13838 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13990 =
                                     let uu____13991 =
                                       let uu____13996 =
                                         let uu____13997 =
                                           let uu____14000 =
                                             let uu____14005 =
                                               let uu____14006 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14006]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14005
                                              in
                                           uu____14000
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13997
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13996)  in
                                     TERM uu____13991  in
                                   [uu____13990]  in
                                 let uu____14027 =
                                   let uu____14034 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14034 with
                                   | (p1,wl3) ->
                                       let uu____14051 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14051 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14027 with
                                  | (sub_probs,wl3) ->
                                      let uu____14078 =
                                        let uu____14079 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14079  in
                                      solve env1 uu____14078))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14112 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14112 with
                | (uu____14127,args) ->
                    (match args with | [] -> false | uu____14155 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14170 =
                  let uu____14171 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14171.FStar_Syntax_Syntax.n  in
                match uu____14170 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14174 -> true
                | uu____14187 -> false  in
              let uu____14188 = quasi_pattern env1 lhs1  in
              match uu____14188 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14199 =
                    let uu____14200 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14200
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14199
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14207 = is_app rhs1  in
                  if uu____14207
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14209 = is_arrow rhs1  in
                     if uu____14209
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14211 =
                          let uu____14212 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14212
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14211))
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
                let uu____14215 = lhs  in
                (match uu____14215 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14219 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14219 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14234 =
                              let uu____14237 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14237
                               in
                            FStar_All.pipe_right uu____14234
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14252 = occurs_check ctx_uv rhs1  in
                          (match uu____14252 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14274 =
                                   let uu____14275 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14275
                                    in
                                 giveup_or_defer env orig wl uu____14274
                               else
                                 (let uu____14277 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14277
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14282 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14282
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14284 =
                                         let uu____14285 =
                                           names_to_string1 fvs2  in
                                         let uu____14286 =
                                           names_to_string1 fvs1  in
                                         let uu____14287 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14285 uu____14286
                                           uu____14287
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14284)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14293 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14297 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14297 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14320 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14320
                             | (FStar_Util.Inl msg,uu____14322) ->
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
                  (let uu____14351 =
                     let uu____14368 = quasi_pattern env lhs  in
                     let uu____14375 = quasi_pattern env rhs  in
                     (uu____14368, uu____14375)  in
                   match uu____14351 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14418 = lhs  in
                       (match uu____14418 with
                        | ({ FStar_Syntax_Syntax.n = uu____14419;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14421;_},u_lhs,uu____14423)
                            ->
                            let uu____14426 = rhs  in
                            (match uu____14426 with
                             | (uu____14427,u_rhs,uu____14429) ->
                                 let uu____14430 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14430
                                 then
                                   let uu____14431 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14431
                                 else
                                   (let uu____14433 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14433 with
                                    | (sub_prob,wl1) ->
                                        let uu____14444 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14444 with
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
                                             let uu____14472 =
                                               let uu____14479 =
                                                 let uu____14482 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14482
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
                                                 uu____14479
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14472 with
                                              | (uu____14485,w,wl2) ->
                                                  let w_app =
                                                    let uu____14491 =
                                                      let uu____14496 =
                                                        FStar_List.map
                                                          (fun uu____14505 
                                                             ->
                                                             match uu____14505
                                                             with
                                                             | (z,uu____14511)
                                                                 ->
                                                                 let uu____14512
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14512)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14496
                                                       in
                                                    uu____14491
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14516 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14516
                                                    then
                                                      let uu____14517 =
                                                        let uu____14520 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14521 =
                                                          let uu____14524 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14525 =
                                                            let uu____14528 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14529 =
                                                              let uu____14532
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14537
                                                                =
                                                                let uu____14540
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14545
                                                                  =
                                                                  let uu____14548
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14548]
                                                                   in
                                                                uu____14540
                                                                  ::
                                                                  uu____14545
                                                                 in
                                                              uu____14532 ::
                                                                uu____14537
                                                               in
                                                            uu____14528 ::
                                                              uu____14529
                                                             in
                                                          uu____14524 ::
                                                            uu____14525
                                                           in
                                                        uu____14520 ::
                                                          uu____14521
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14517
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14554 =
                                                          let uu____14559 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14559)
                                                           in
                                                        TERM uu____14554  in
                                                      let uu____14560 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14560
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14565 =
                                                             let uu____14570
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
                                                               uu____14570)
                                                              in
                                                           TERM uu____14565
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14571 =
                                                      let uu____14572 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14572
                                                       in
                                                    solve env uu____14571)))))))
                   | uu____14573 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____14641 = head_matches_delta env1 wl1 t1 t2  in
           match uu____14641 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____14672,uu____14673) ->
                    let rec may_relate head3 =
                      let uu____14700 =
                        let uu____14701 = FStar_Syntax_Subst.compress head3
                           in
                        uu____14701.FStar_Syntax_Syntax.n  in
                      match uu____14700 with
                      | FStar_Syntax_Syntax.Tm_name uu____14704 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____14705 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14728;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____14729;
                            FStar_Syntax_Syntax.fv_qual = uu____14730;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14733;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____14734;
                            FStar_Syntax_Syntax.fv_qual = uu____14735;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____14739,uu____14740) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____14782) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____14788) ->
                          may_relate t
                      | uu____14793 -> false  in
                    let uu____14794 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____14794
                    then
                      let uu____14795 =
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
                                 let uu____14827 =
                                   let uu____14828 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____14828 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____14827
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____14833 = has_type_guard t1 t2  in
                             (uu____14833, wl1)
                           else
                             (let uu____14839 = has_type_guard t2 t1  in
                              (uu____14839, wl1)))
                         in
                      (match uu____14795 with
                       | (guard,wl2) ->
                           let uu____14846 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____14846)
                    else
                      (let uu____14848 =
                         let uu____14849 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14850 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____14849 uu____14850
                          in
                       giveup env1 uu____14848 orig)
                | (uu____14851,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___187_14865 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___187_14865.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___187_14865.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___187_14865.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___187_14865.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___187_14865.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___187_14865.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___187_14865.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___187_14865.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____14866,FStar_Pervasives_Native.None ) ->
                    ((let uu____14878 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14878
                      then
                        let uu____14879 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____14880 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____14881 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____14882 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____14879 uu____14880 uu____14881 uu____14882
                      else ());
                     (let uu____14884 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____14884 with
                      | (head11,args1) ->
                          let uu____14921 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____14921 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____14975 =
                                   let uu____14976 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____14977 = args_to_string args1  in
                                   let uu____14978 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____14979 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____14976 uu____14977 uu____14978
                                     uu____14979
                                    in
                                 giveup env1 uu____14975 orig
                               else
                                 (let uu____14981 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____14988 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____14988 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____14981
                                  then
                                    let uu____14989 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____14989 with
                                    | USolved wl2 ->
                                        let uu____14991 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____14991
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____14995 =
                                       base_and_refinement env1 t1  in
                                     match uu____14995 with
                                     | (base1,refinement1) ->
                                         let uu____15020 =
                                           base_and_refinement env1 t2  in
                                         (match uu____15020 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____15077 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____15077 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____15081 =
                                                          FStar_List.fold_right2
                                                            (fun uu____15114 
                                                               ->
                                                               fun
                                                                 uu____15115 
                                                                 ->
                                                                 fun
                                                                   uu____15116
                                                                    ->
                                                                   match 
                                                                    (uu____15114,
                                                                    uu____15115,
                                                                    uu____15116)
                                                                   with
                                                                   | 
                                                                   ((a,uu____15152),
                                                                    (a',uu____15154),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____15175
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____15175
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
                                                        (match uu____15081
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____15203
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____15203
                                                               then
                                                                 let uu____15204
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____15204
                                                               else ());
                                                              (let formula =
                                                                 let uu____15209
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____15209
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
                                               | uu____15217 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___188_15257 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___188_15257.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15260 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15260
          then
            let uu____15261 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15261
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15266 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15266
              then
                let uu____15267 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15268 =
                  let uu____15269 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15270 =
                    let uu____15271 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15271  in
                  Prims.strcat uu____15269 uu____15270  in
                let uu____15272 =
                  let uu____15273 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15274 =
                    let uu____15275 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15275  in
                  Prims.strcat uu____15273 uu____15274  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15267
                  uu____15268 uu____15272
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15278,uu____15279) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15304,FStar_Syntax_Syntax.Tm_delayed uu____15305) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15330,uu____15331) ->
                  let uu____15358 =
                    let uu___189_15359 = problem  in
                    let uu____15360 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___189_15359.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15360;
                      FStar_TypeChecker_Common.relation =
                        (uu___189_15359.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___189_15359.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___189_15359.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___189_15359.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___189_15359.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___189_15359.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___189_15359.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___189_15359.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15358 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15361,uu____15362) ->
                  let uu____15369 =
                    let uu___190_15370 = problem  in
                    let uu____15371 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___190_15370.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15371;
                      FStar_TypeChecker_Common.relation =
                        (uu___190_15370.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___190_15370.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___190_15370.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___190_15370.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___190_15370.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___190_15370.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___190_15370.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___190_15370.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15369 wl
              | (uu____15372,FStar_Syntax_Syntax.Tm_ascribed uu____15373) ->
                  let uu____15400 =
                    let uu___191_15401 = problem  in
                    let uu____15402 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___191_15401.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___191_15401.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___191_15401.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15402;
                      FStar_TypeChecker_Common.element =
                        (uu___191_15401.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___191_15401.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___191_15401.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___191_15401.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___191_15401.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___191_15401.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15400 wl
              | (uu____15403,FStar_Syntax_Syntax.Tm_meta uu____15404) ->
                  let uu____15411 =
                    let uu___192_15412 = problem  in
                    let uu____15413 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___192_15412.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___192_15412.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___192_15412.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15413;
                      FStar_TypeChecker_Common.element =
                        (uu___192_15412.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___192_15412.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___192_15412.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___192_15412.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___192_15412.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___192_15412.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15411 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15415),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15417)) ->
                  let uu____15426 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15426
              | (FStar_Syntax_Syntax.Tm_bvar uu____15427,uu____15428) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15429,FStar_Syntax_Syntax.Tm_bvar uu____15430) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___146_15489 =
                    match uu___146_15489 with
                    | [] -> c
                    | bs ->
                        let uu____15511 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15511
                     in
                  let uu____15520 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15520 with
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
                                    let uu____15643 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15643
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
                  let mk_t t l uu___147_15718 =
                    match uu___147_15718 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15752 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15752 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____15871 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____15872 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____15871
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____15872 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____15873,uu____15874) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15901 -> true
                    | uu____15918 -> false  in
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
                      (let uu____15959 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___193_15967 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___193_15967.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___193_15967.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___193_15967.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___193_15967.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___193_15967.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___193_15967.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___193_15967.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___193_15967.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___193_15967.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___193_15967.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___193_15967.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___193_15967.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___193_15967.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___193_15967.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___193_15967.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___193_15967.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___193_15967.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___193_15967.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___193_15967.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___193_15967.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___193_15967.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___193_15967.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___193_15967.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___193_15967.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___193_15967.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___193_15967.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___193_15967.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___193_15967.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___193_15967.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___193_15967.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___193_15967.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___193_15967.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___193_15967.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___193_15967.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___193_15967.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___193_15967.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15959 with
                       | (uu____15970,ty,uu____15972) ->
                           let uu____15973 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15973)
                     in
                  let uu____15974 =
                    let uu____15987 = maybe_eta t1  in
                    let uu____15992 = maybe_eta t2  in
                    (uu____15987, uu____15992)  in
                  (match uu____15974 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___194_16016 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___194_16016.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___194_16016.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___194_16016.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___194_16016.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___194_16016.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___194_16016.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___194_16016.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___194_16016.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16027 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16027
                       then
                         let uu____16028 = destruct_flex_t not_abs wl  in
                         (match uu____16028 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16043 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16043.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16043.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16043.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16043.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16043.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16043.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16043.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16043.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16055 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16055
                       then
                         let uu____16056 = destruct_flex_t not_abs wl  in
                         (match uu____16056 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16071 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16071.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16071.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16071.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16071.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16071.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16071.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16071.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16071.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16073 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16086,FStar_Syntax_Syntax.Tm_abs uu____16087) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16114 -> true
                    | uu____16131 -> false  in
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
                      (let uu____16172 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___193_16180 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___193_16180.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___193_16180.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___193_16180.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___193_16180.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___193_16180.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___193_16180.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___193_16180.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___193_16180.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___193_16180.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___193_16180.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___193_16180.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___193_16180.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___193_16180.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___193_16180.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___193_16180.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___193_16180.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___193_16180.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___193_16180.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___193_16180.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___193_16180.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___193_16180.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___193_16180.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___193_16180.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___193_16180.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___193_16180.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___193_16180.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___193_16180.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___193_16180.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___193_16180.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___193_16180.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___193_16180.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___193_16180.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___193_16180.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___193_16180.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___193_16180.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___193_16180.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16172 with
                       | (uu____16183,ty,uu____16185) ->
                           let uu____16186 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16186)
                     in
                  let uu____16187 =
                    let uu____16200 = maybe_eta t1  in
                    let uu____16205 = maybe_eta t2  in
                    (uu____16200, uu____16205)  in
                  (match uu____16187 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___194_16229 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___194_16229.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___194_16229.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___194_16229.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___194_16229.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___194_16229.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___194_16229.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___194_16229.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___194_16229.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16240 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16240
                       then
                         let uu____16241 = destruct_flex_t not_abs wl  in
                         (match uu____16241 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16256 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16256.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16256.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16256.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16256.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16256.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16256.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16256.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16256.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16268 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16268
                       then
                         let uu____16269 = destruct_flex_t not_abs wl  in
                         (match uu____16269 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___195_16284 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___195_16284.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___195_16284.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___195_16284.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___195_16284.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___195_16284.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___195_16284.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___195_16284.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___195_16284.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16286 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16314 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16314) &&
                       (let uu____16318 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16318))
                      &&
                      (let uu____16325 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16325 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___148_16337 =
                             match uu___148_16337 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16338 -> true
                             | uu____16339 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16340 -> false)
                     in
                  let uu____16341 = as_refinement should_delta env wl t1  in
                  (match uu____16341 with
                   | (x11,phi1) ->
                       let uu____16348 = as_refinement should_delta env wl t2
                          in
                       (match uu____16348 with
                        | (x21,phi21) ->
                            let uu____16355 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16355 with
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
                                   let uu____16421 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16421
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16433 =
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
                                 let has_uvars =
                                   (let uu____16447 =
                                      let uu____16448 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16448  in
                                    Prims.op_Negation uu____16447) ||
                                     (let uu____16452 =
                                        let uu____16453 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16453
                                         in
                                      Prims.op_Negation uu____16452)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16456 =
                                     let uu____16461 =
                                       let uu____16468 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16468]  in
                                     mk_t_problem wl1 uu____16461 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16456 with
                                    | (ref_prob,wl2) ->
                                        let uu____16483 =
                                          solve env1
                                            (let uu___196_16485 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___196_16485.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___196_16485.smt_ok);
                                               tcenv = (uu___196_16485.tcenv);
                                               wl_implicits =
                                                 (uu___196_16485.wl_implicits)
                                             })
                                           in
                                        (match uu____16483 with
                                         | Failed (prob,msg) ->
                                             if
                                               (Prims.op_Negation
                                                  env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                 && has_uvars
                                             then giveup env1 msg prob
                                             else fallback ()
                                         | Success uu____16495 ->
                                             let guard =
                                               let uu____16503 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16503
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___197_16512 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___197_16512.attempting);
                                                 wl_deferred =
                                                   (uu___197_16512.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___197_16512.defer_ok);
                                                 smt_ok =
                                                   (uu___197_16512.smt_ok);
                                                 tcenv =
                                                   (uu___197_16512.tcenv);
                                                 wl_implicits =
                                                   (uu___197_16512.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16514,FStar_Syntax_Syntax.Tm_uvar uu____16515) ->
                  let uu____16544 = destruct_flex_t t1 wl  in
                  (match uu____16544 with
                   | (f1,wl1) ->
                       let uu____16551 = destruct_flex_t t2 wl1  in
                       (match uu____16551 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16558;
                    FStar_Syntax_Syntax.pos = uu____16559;
                    FStar_Syntax_Syntax.vars = uu____16560;_},uu____16561),FStar_Syntax_Syntax.Tm_uvar
                 uu____16562) ->
                  let uu____16611 = destruct_flex_t t1 wl  in
                  (match uu____16611 with
                   | (f1,wl1) ->
                       let uu____16618 = destruct_flex_t t2 wl1  in
                       (match uu____16618 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16625,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16626;
                    FStar_Syntax_Syntax.pos = uu____16627;
                    FStar_Syntax_Syntax.vars = uu____16628;_},uu____16629))
                  ->
                  let uu____16678 = destruct_flex_t t1 wl  in
                  (match uu____16678 with
                   | (f1,wl1) ->
                       let uu____16685 = destruct_flex_t t2 wl1  in
                       (match uu____16685 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16692;
                    FStar_Syntax_Syntax.pos = uu____16693;
                    FStar_Syntax_Syntax.vars = uu____16694;_},uu____16695),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16696;
                    FStar_Syntax_Syntax.pos = uu____16697;
                    FStar_Syntax_Syntax.vars = uu____16698;_},uu____16699))
                  ->
                  let uu____16768 = destruct_flex_t t1 wl  in
                  (match uu____16768 with
                   | (f1,wl1) ->
                       let uu____16775 = destruct_flex_t t2 wl1  in
                       (match uu____16775 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16782,uu____16783) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16798 = destruct_flex_t t1 wl  in
                  (match uu____16798 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16805;
                    FStar_Syntax_Syntax.pos = uu____16806;
                    FStar_Syntax_Syntax.vars = uu____16807;_},uu____16808),uu____16809)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16844 = destruct_flex_t t1 wl  in
                  (match uu____16844 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____16851,FStar_Syntax_Syntax.Tm_uvar uu____16852) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____16867,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16868;
                    FStar_Syntax_Syntax.pos = uu____16869;
                    FStar_Syntax_Syntax.vars = uu____16870;_},uu____16871))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16906,FStar_Syntax_Syntax.Tm_arrow uu____16907) ->
                  solve_t' env
                    (let uu___198_16935 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16935.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16935.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___198_16935.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___198_16935.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16935.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___198_16935.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16935.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16935.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16935.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16936;
                    FStar_Syntax_Syntax.pos = uu____16937;
                    FStar_Syntax_Syntax.vars = uu____16938;_},uu____16939),FStar_Syntax_Syntax.Tm_arrow
                 uu____16940) ->
                  solve_t' env
                    (let uu___198_16988 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___198_16988.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___198_16988.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___198_16988.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___198_16988.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___198_16988.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___198_16988.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___198_16988.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___198_16988.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___198_16988.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____16989,FStar_Syntax_Syntax.Tm_uvar uu____16990) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____17005,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17006;
                    FStar_Syntax_Syntax.pos = uu____17007;
                    FStar_Syntax_Syntax.vars = uu____17008;_},uu____17009))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____17044,uu____17045) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17060;
                    FStar_Syntax_Syntax.pos = uu____17061;
                    FStar_Syntax_Syntax.vars = uu____17062;_},uu____17063),uu____17064)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17099,uu____17100) ->
                  let t21 =
                    let uu____17108 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17108  in
                  solve_t env
                    (let uu___199_17134 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___199_17134.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___199_17134.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___199_17134.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___199_17134.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___199_17134.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___199_17134.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___199_17134.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___199_17134.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___199_17134.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17135,FStar_Syntax_Syntax.Tm_refine uu____17136) ->
                  let t11 =
                    let uu____17144 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17144  in
                  solve_t env
                    (let uu___200_17170 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___200_17170.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___200_17170.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___200_17170.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___200_17170.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___200_17170.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___200_17170.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___200_17170.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___200_17170.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___200_17170.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____17247 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____17247 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____17468 = br1  in
                             (match uu____17468 with
                              | (p1,w1,uu____17493) ->
                                  let uu____17510 = br2  in
                                  (match uu____17510 with
                                   | (p2,w2,uu____17529) ->
                                       let uu____17534 =
                                         let uu____17535 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____17535  in
                                       if uu____17534
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____17551 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____17551 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____17584 = br2  in
                                              (match uu____17584 with
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
                                                     let uu____17619 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____17619
                                                      in
                                                   let uu____17630 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____17653,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____17670) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____17713 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____17713
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____17630
                                                     (fun uu____17755  ->
                                                        match uu____17755
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____17776 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____17776
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____17791
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____17791
                                                                   (fun
                                                                    uu____17815
                                                                     ->
                                                                    match uu____17815
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
                         | uu____17900 -> FStar_Pervasives_Native.None  in
                       let uu____17937 = solve_branches wl1 brs1 brs2  in
                       (match uu____17937 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____17968,uu____17969) ->
                  let head1 =
                    let uu____17993 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17993
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18033 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18033
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18073 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18073
                    then
                      let uu____18074 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18075 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18076 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18074 uu____18075 uu____18076
                    else ());
                   (let uu____18078 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18078
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18085 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18085
                       then
                         let uu____18086 =
                           let uu____18093 =
                             let uu____18094 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18094 = FStar_Syntax_Util.Equal  in
                           if uu____18093
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18104 = mk_eq2 wl orig t1 t2  in
                              match uu____18104 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18086 with
                         | (guard,wl1) ->
                             let uu____18125 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18125
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18128,uu____18129) ->
                  let head1 =
                    let uu____18137 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18137
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18177 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18177
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18217 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18217
                    then
                      let uu____18218 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18219 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18220 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18218 uu____18219 uu____18220
                    else ());
                   (let uu____18222 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18222
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18229 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18229
                       then
                         let uu____18230 =
                           let uu____18237 =
                             let uu____18238 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18238 = FStar_Syntax_Util.Equal  in
                           if uu____18237
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18248 = mk_eq2 wl orig t1 t2  in
                              match uu____18248 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18230 with
                         | (guard,wl1) ->
                             let uu____18269 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18269
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18272,uu____18273) ->
                  let head1 =
                    let uu____18275 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18275
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18315 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18315
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18355 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18355
                    then
                      let uu____18356 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18357 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18358 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18356 uu____18357 uu____18358
                    else ());
                   (let uu____18360 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18360
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18367 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18367
                       then
                         let uu____18368 =
                           let uu____18375 =
                             let uu____18376 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18376 = FStar_Syntax_Util.Equal  in
                           if uu____18375
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18386 = mk_eq2 wl orig t1 t2  in
                              match uu____18386 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18368 with
                         | (guard,wl1) ->
                             let uu____18407 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18407
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18410,uu____18411) ->
                  let head1 =
                    let uu____18413 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18413
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18453 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18453
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18493 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18493
                    then
                      let uu____18494 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18495 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18496 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18494 uu____18495 uu____18496
                    else ());
                   (let uu____18498 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18498
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18505 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18505
                       then
                         let uu____18506 =
                           let uu____18513 =
                             let uu____18514 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18514 = FStar_Syntax_Util.Equal  in
                           if uu____18513
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18524 = mk_eq2 wl orig t1 t2  in
                              match uu____18524 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18506 with
                         | (guard,wl1) ->
                             let uu____18545 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18545
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18548,uu____18549) ->
                  let head1 =
                    let uu____18551 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18551
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18591 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18591
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18631 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18631
                    then
                      let uu____18632 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18633 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18634 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18632 uu____18633 uu____18634
                    else ());
                   (let uu____18636 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18636
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18643 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18643
                       then
                         let uu____18644 =
                           let uu____18651 =
                             let uu____18652 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18652 = FStar_Syntax_Util.Equal  in
                           if uu____18651
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18662 = mk_eq2 wl orig t1 t2  in
                              match uu____18662 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18644 with
                         | (guard,wl1) ->
                             let uu____18683 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18683
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____18686,uu____18687) ->
                  let head1 =
                    let uu____18703 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18703
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18743 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18743
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18783 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18783
                    then
                      let uu____18784 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18785 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18786 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18784 uu____18785 uu____18786
                    else ());
                   (let uu____18788 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18788
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18795 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18795
                       then
                         let uu____18796 =
                           let uu____18803 =
                             let uu____18804 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18804 = FStar_Syntax_Util.Equal  in
                           if uu____18803
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18814 = mk_eq2 wl orig t1 t2  in
                              match uu____18814 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18796 with
                         | (guard,wl1) ->
                             let uu____18835 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18835
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18838,FStar_Syntax_Syntax.Tm_match uu____18839) ->
                  let head1 =
                    let uu____18863 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18863
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18903 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18903
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18943 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18943
                    then
                      let uu____18944 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18945 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18946 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18944 uu____18945 uu____18946
                    else ());
                   (let uu____18948 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18948
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18955 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18955
                       then
                         let uu____18956 =
                           let uu____18963 =
                             let uu____18964 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18964 = FStar_Syntax_Util.Equal  in
                           if uu____18963
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18974 = mk_eq2 wl orig t1 t2  in
                              match uu____18974 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18956 with
                         | (guard,wl1) ->
                             let uu____18995 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18995
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18998,FStar_Syntax_Syntax.Tm_uinst uu____18999) ->
                  let head1 =
                    let uu____19007 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19007
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19047 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19047
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19087 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19087
                    then
                      let uu____19088 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19089 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19090 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19088 uu____19089 uu____19090
                    else ());
                   (let uu____19092 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19092
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19099 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19099
                       then
                         let uu____19100 =
                           let uu____19107 =
                             let uu____19108 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19108 = FStar_Syntax_Util.Equal  in
                           if uu____19107
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19118 = mk_eq2 wl orig t1 t2  in
                              match uu____19118 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19100 with
                         | (guard,wl1) ->
                             let uu____19139 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19139
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19142,FStar_Syntax_Syntax.Tm_name uu____19143) ->
                  let head1 =
                    let uu____19145 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19145
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19185 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19185
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19225 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19225
                    then
                      let uu____19226 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19227 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19228 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19226 uu____19227 uu____19228
                    else ());
                   (let uu____19230 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19230
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19237 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19237
                       then
                         let uu____19238 =
                           let uu____19245 =
                             let uu____19246 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19246 = FStar_Syntax_Util.Equal  in
                           if uu____19245
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19256 = mk_eq2 wl orig t1 t2  in
                              match uu____19256 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19238 with
                         | (guard,wl1) ->
                             let uu____19277 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19277
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19280,FStar_Syntax_Syntax.Tm_constant uu____19281) ->
                  let head1 =
                    let uu____19283 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19283
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19323 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19323
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19363 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19363
                    then
                      let uu____19364 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19365 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19366 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19364 uu____19365 uu____19366
                    else ());
                   (let uu____19368 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19368
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19375 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19375
                       then
                         let uu____19376 =
                           let uu____19383 =
                             let uu____19384 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19384 = FStar_Syntax_Util.Equal  in
                           if uu____19383
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19394 = mk_eq2 wl orig t1 t2  in
                              match uu____19394 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19376 with
                         | (guard,wl1) ->
                             let uu____19415 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19415
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19418,FStar_Syntax_Syntax.Tm_fvar uu____19419) ->
                  let head1 =
                    let uu____19421 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19421
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19461 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19461
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19501 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19501
                    then
                      let uu____19502 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19503 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19504 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19502 uu____19503 uu____19504
                    else ());
                   (let uu____19506 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19506
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19513 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19513
                       then
                         let uu____19514 =
                           let uu____19521 =
                             let uu____19522 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19522 = FStar_Syntax_Util.Equal  in
                           if uu____19521
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19532 = mk_eq2 wl orig t1 t2  in
                              match uu____19532 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19514 with
                         | (guard,wl1) ->
                             let uu____19553 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19553
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19556,FStar_Syntax_Syntax.Tm_app uu____19557) ->
                  let head1 =
                    let uu____19573 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19573
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19613 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19613
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19653 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19653
                    then
                      let uu____19654 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19655 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19656 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19654 uu____19655 uu____19656
                    else ());
                   (let uu____19658 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19658
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19665 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19665
                       then
                         let uu____19666 =
                           let uu____19673 =
                             let uu____19674 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19674 = FStar_Syntax_Util.Equal  in
                           if uu____19673
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19684 = mk_eq2 wl orig t1 t2  in
                              match uu____19684 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19666 with
                         | (guard,wl1) ->
                             let uu____19705 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19705
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____19708,FStar_Syntax_Syntax.Tm_let uu____19709) ->
                  let uu____19734 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____19734
                  then
                    let uu____19735 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____19735
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____19737,uu____19738) ->
                  let uu____19751 =
                    let uu____19756 =
                      let uu____19757 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19758 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19759 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19760 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19757 uu____19758 uu____19759 uu____19760
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19756)
                     in
                  FStar_Errors.raise_error uu____19751
                    t1.FStar_Syntax_Syntax.pos
              | (uu____19761,FStar_Syntax_Syntax.Tm_let uu____19762) ->
                  let uu____19775 =
                    let uu____19780 =
                      let uu____19781 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19782 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19783 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19784 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19781 uu____19782 uu____19783 uu____19784
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19780)
                     in
                  FStar_Errors.raise_error uu____19775
                    t1.FStar_Syntax_Syntax.pos
              | uu____19785 -> giveup env "head tag mismatch" orig))))

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
          (let uu____19844 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____19844
           then
             let uu____19845 =
               let uu____19846 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____19846  in
             let uu____19847 =
               let uu____19848 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____19848  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____19845 uu____19847
           else ());
          (let uu____19850 =
             let uu____19851 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____19851  in
           if uu____19850
           then
             let uu____19852 =
               let uu____19853 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____19854 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____19853 uu____19854
                in
             giveup env uu____19852 orig
           else
             (let uu____19856 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____19856 with
              | (ret_sub_prob,wl1) ->
                  let uu____19863 =
                    FStar_List.fold_right2
                      (fun uu____19896  ->
                         fun uu____19897  ->
                           fun uu____19898  ->
                             match (uu____19896, uu____19897, uu____19898)
                             with
                             | ((a1,uu____19934),(a2,uu____19936),(arg_sub_probs,wl2))
                                 ->
                                 let uu____19957 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____19957 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____19863 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____19986 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____19986  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20016 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20019)::[] -> wp1
              | uu____20036 ->
                  let uu____20045 =
                    let uu____20046 =
                      let uu____20047 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20047  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20046
                     in
                  failwith uu____20045
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20053 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20053]
              | x -> x  in
            let uu____20055 =
              let uu____20064 =
                let uu____20071 =
                  let uu____20072 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20072 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20071  in
              [uu____20064]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20055;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20085 = lift_c1 ()  in solve_eq uu____20085 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___149_20091  ->
                       match uu___149_20091 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20092 -> false))
                in
             let uu____20093 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20119)::uu____20120,(wp2,uu____20122)::uu____20123)
                   -> (wp1, wp2)
               | uu____20176 ->
                   let uu____20197 =
                     let uu____20202 =
                       let uu____20203 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20204 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20203 uu____20204
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20202)
                      in
                   FStar_Errors.raise_error uu____20197
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20093 with
             | (wpc1,wpc2) ->
                 let uu____20211 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20211
                 then
                   let uu____20214 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20214 wl
                 else
                   (let uu____20216 =
                      let uu____20223 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20223  in
                    match uu____20216 with
                    | (c2_decl,qualifiers) ->
                        let uu____20244 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20244
                        then
                          let c1_repr =
                            let uu____20248 =
                              let uu____20249 =
                                let uu____20250 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20250  in
                              let uu____20251 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20249 uu____20251
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20248
                             in
                          let c2_repr =
                            let uu____20253 =
                              let uu____20254 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20255 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20254 uu____20255
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20253
                             in
                          let uu____20256 =
                            let uu____20261 =
                              let uu____20262 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20263 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20262 uu____20263
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20261
                             in
                          (match uu____20256 with
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
                                 ((let uu____20277 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20277
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20280 =
                                     let uu____20287 =
                                       let uu____20288 =
                                         let uu____20303 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20306 =
                                           let uu____20315 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20322 =
                                             let uu____20331 =
                                               let uu____20338 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20338
                                                in
                                             [uu____20331]  in
                                           uu____20315 :: uu____20322  in
                                         (uu____20303, uu____20306)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20288
                                        in
                                     FStar_Syntax_Syntax.mk uu____20287  in
                                   uu____20280 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20373 =
                                    let uu____20380 =
                                      let uu____20381 =
                                        let uu____20396 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20399 =
                                          let uu____20408 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20415 =
                                            let uu____20424 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20431 =
                                              let uu____20440 =
                                                let uu____20447 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20447
                                                 in
                                              [uu____20440]  in
                                            uu____20424 :: uu____20431  in
                                          uu____20408 :: uu____20415  in
                                        (uu____20396, uu____20399)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20381
                                       in
                                    FStar_Syntax_Syntax.mk uu____20380  in
                                  uu____20373 FStar_Pervasives_Native.None r)
                              in
                           let uu____20485 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20485 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20493 =
                                   let uu____20496 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____20496
                                    in
                                 solve_prob orig uu____20493 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____20503 = FStar_Util.physical_equality c1 c2  in
        if uu____20503
        then
          let uu____20504 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20504
        else
          ((let uu____20507 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20507
            then
              let uu____20508 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20509 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20508
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20509
            else ());
           (let uu____20511 =
              let uu____20520 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20523 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20520, uu____20523)  in
            match uu____20511 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20541),FStar_Syntax_Syntax.Total
                    (t2,uu____20543)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20560 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20560 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20561,FStar_Syntax_Syntax.Total uu____20562) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20580),FStar_Syntax_Syntax.Total
                    (t2,uu____20582)) ->
                     let uu____20599 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20599 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20601),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20603)) ->
                     let uu____20620 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20620 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20622),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20624)) ->
                     let uu____20641 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20641 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20642,FStar_Syntax_Syntax.Comp uu____20643) ->
                     let uu____20652 =
                       let uu___201_20655 = problem  in
                       let uu____20658 =
                         let uu____20659 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20659
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20655.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20658;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20655.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_20655.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_20655.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20655.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20655.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20655.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20655.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20655.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20652 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20660,FStar_Syntax_Syntax.Comp uu____20661) ->
                     let uu____20670 =
                       let uu___201_20673 = problem  in
                       let uu____20676 =
                         let uu____20677 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20677
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___201_20673.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20676;
                         FStar_TypeChecker_Common.relation =
                           (uu___201_20673.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___201_20673.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___201_20673.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___201_20673.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___201_20673.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___201_20673.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___201_20673.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___201_20673.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20670 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20678,FStar_Syntax_Syntax.GTotal uu____20679) ->
                     let uu____20688 =
                       let uu___202_20691 = problem  in
                       let uu____20694 =
                         let uu____20695 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20695
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20691.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_20691.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20691.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20694;
                         FStar_TypeChecker_Common.element =
                           (uu___202_20691.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20691.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20691.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20691.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20691.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20691.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20688 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20696,FStar_Syntax_Syntax.Total uu____20697) ->
                     let uu____20706 =
                       let uu___202_20709 = problem  in
                       let uu____20712 =
                         let uu____20713 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20713
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20709.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___202_20709.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20709.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20712;
                         FStar_TypeChecker_Common.element =
                           (uu___202_20709.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20709.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20709.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20709.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20709.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20709.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20706 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20714,FStar_Syntax_Syntax.Comp uu____20715) ->
                     let uu____20716 =
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
                     if uu____20716
                     then
                       let uu____20717 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____20717 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20721 =
                            let uu____20726 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____20726
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20732 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____20733 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____20732, uu____20733))
                             in
                          match uu____20721 with
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
                           (let uu____20740 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____20740
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20742 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____20742 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20745 =
                                  let uu____20746 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____20747 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____20746 uu____20747
                                   in
                                giveup env uu____20745 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____20754 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20782  ->
              match uu____20782 with
              | (uu____20791,tm,uu____20793,uu____20794) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____20754 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____20827 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____20827 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____20845 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____20873  ->
                match uu____20873 with
                | (u1,u2) ->
                    let uu____20880 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____20881 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____20880 uu____20881))
         in
      FStar_All.pipe_right uu____20845 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____20908,[])) -> "{}"
      | uu____20933 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____20956 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____20956
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____20959 =
              FStar_List.map
                (fun uu____20969  ->
                   match uu____20969 with
                   | (uu____20974,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____20959 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____20979 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____20979 imps
  
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
                  let uu____21032 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21032
                  then
                    let uu____21033 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21034 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21033
                      (rel_to_string rel) uu____21034
                  else "TOP"  in
                let uu____21036 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21036 with
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
              let uu____21093 =
                let uu____21096 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____21096
                 in
              FStar_Syntax_Syntax.new_bv uu____21093 t1  in
            let uu____21099 =
              let uu____21104 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21104
               in
            match uu____21099 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____21160 = FStar_Options.eager_inference ()  in
          if uu____21160
          then
            let uu___203_21161 = probs  in
            {
              attempting = (uu___203_21161.attempting);
              wl_deferred = (uu___203_21161.wl_deferred);
              ctr = (uu___203_21161.ctr);
              defer_ok = false;
              smt_ok = (uu___203_21161.smt_ok);
              tcenv = (uu___203_21161.tcenv);
              wl_implicits = (uu___203_21161.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21181 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21181
              then
                let uu____21182 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21182
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
          ((let uu____21204 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21204
            then
              let uu____21205 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21205
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21209 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21209
             then
               let uu____21210 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21210
             else ());
            (let f2 =
               let uu____21213 =
                 let uu____21214 = FStar_Syntax_Util.unmeta f1  in
                 uu____21214.FStar_Syntax_Syntax.n  in
               match uu____21213 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21218 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___204_21219 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___204_21219.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___204_21219.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___204_21219.FStar_TypeChecker_Env.implicits)
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
            let uu____21321 =
              let uu____21322 =
                let uu____21323 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21323;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21322  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____21321
  
let with_guard_no_simp :
  'Auu____21338 .
    'Auu____21338 ->
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
            let uu____21361 =
              let uu____21362 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21362;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21361
  
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
          (let uu____21400 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21400
           then
             let uu____21401 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21402 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21401
               uu____21402
           else ());
          (let uu____21404 =
             let uu____21409 = empty_worklist env  in
             let uu____21410 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____21409 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____21410
              in
           match uu____21404 with
           | (prob,wl) ->
               let g =
                 let uu____21418 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21436  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21418  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21478 = try_teq true env t1 t2  in
        match uu____21478 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21482 = FStar_TypeChecker_Env.get_range env  in
              let uu____21483 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21482 uu____21483);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21490 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21490
              then
                let uu____21491 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21492 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21493 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21491
                  uu____21492 uu____21493
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
          let uu____21515 = FStar_TypeChecker_Env.get_range env  in
          let uu____21516 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21515 uu____21516
  
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
        (let uu____21541 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21541
         then
           let uu____21542 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21543 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21542 uu____21543
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21546 =
           let uu____21553 = empty_worklist env  in
           let uu____21554 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____21553 env c1 rel c2 FStar_Pervasives_Native.None
             uu____21554 "sub_comp"
            in
         match uu____21546 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21564 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21582  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21564)
  
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
      fun uu____21635  ->
        match uu____21635 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21678 =
                 let uu____21683 =
                   let uu____21684 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21685 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21684 uu____21685
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21683)  in
               let uu____21686 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21678 uu____21686)
               in
            let equiv1 v1 v' =
              let uu____21698 =
                let uu____21703 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21704 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21703, uu____21704)  in
              match uu____21698 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21723 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21753 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____21753 with
                      | FStar_Syntax_Syntax.U_unif uu____21760 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21789  ->
                                    match uu____21789 with
                                    | (u,v') ->
                                        let uu____21798 = equiv1 v1 v'  in
                                        if uu____21798
                                        then
                                          let uu____21801 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____21801 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____21817 -> []))
               in
            let uu____21822 =
              let wl =
                let uu___205_21826 = empty_worklist env  in
                {
                  attempting = (uu___205_21826.attempting);
                  wl_deferred = (uu___205_21826.wl_deferred);
                  ctr = (uu___205_21826.ctr);
                  defer_ok = false;
                  smt_ok = (uu___205_21826.smt_ok);
                  tcenv = (uu___205_21826.tcenv);
                  wl_implicits = (uu___205_21826.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21844  ->
                      match uu____21844 with
                      | (lb,v1) ->
                          let uu____21851 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____21851 with
                           | USolved wl1 -> ()
                           | uu____21853 -> fail1 lb v1)))
               in
            let rec check_ineq uu____21863 =
              match uu____21863 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21872) -> true
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
                      uu____21895,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21897,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21908) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21915,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21923 -> false)
               in
            let uu____21928 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21943  ->
                      match uu____21943 with
                      | (u,v1) ->
                          let uu____21950 = check_ineq (u, v1)  in
                          if uu____21950
                          then true
                          else
                            ((let uu____21953 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____21953
                              then
                                let uu____21954 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____21955 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____21954
                                  uu____21955
                              else ());
                             false)))
               in
            if uu____21928
            then ()
            else
              ((let uu____21959 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____21959
                then
                  ((let uu____21961 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21961);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21971 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21971))
                else ());
               (let uu____21981 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____21981))
  
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
        let fail1 uu____22048 =
          match uu____22048 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___206_22069 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___206_22069.attempting);
            wl_deferred = (uu___206_22069.wl_deferred);
            ctr = (uu___206_22069.ctr);
            defer_ok;
            smt_ok = (uu___206_22069.smt_ok);
            tcenv = (uu___206_22069.tcenv);
            wl_implicits = (uu___206_22069.wl_implicits)
          }  in
        (let uu____22071 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22071
         then
           let uu____22072 = FStar_Util.string_of_bool defer_ok  in
           let uu____22073 = wl_to_string wl  in
           let uu____22074 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22072 uu____22073 uu____22074
         else ());
        (let g1 =
           let uu____22085 = solve_and_commit env wl fail1  in
           match uu____22085 with
           | FStar_Pervasives_Native.Some
               (uu____22092::uu____22093,uu____22094) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___207_22119 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___207_22119.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___207_22119.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22128 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___208_22136 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___208_22136.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___208_22136.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___208_22136.FStar_TypeChecker_Env.implicits)
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
    let uu____22184 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22184 with
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
            let uu___209_22307 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___209_22307.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___209_22307.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___209_22307.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22308 =
            let uu____22309 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22309  in
          if uu____22308
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22317 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22318 =
                       let uu____22319 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22319
                        in
                     FStar_Errors.diag uu____22317 uu____22318)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22323 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22324 =
                        let uu____22325 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22325
                         in
                      FStar_Errors.diag uu____22323 uu____22324)
                   else ();
                   (let uu____22328 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22328 "discharge_guard'"
                      env vc1);
                   (let uu____22329 = check_trivial vc1  in
                    match uu____22329 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22336 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22337 =
                                let uu____22338 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22338
                                 in
                              FStar_Errors.diag uu____22336 uu____22337)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22343 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22344 =
                                let uu____22345 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22345
                                 in
                              FStar_Errors.diag uu____22343 uu____22344)
                           else ();
                           (let vcs =
                              let uu____22358 = FStar_Options.use_tactics ()
                                 in
                              if uu____22358
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22380  ->
                                     (let uu____22382 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____22382);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22425  ->
                                              match uu____22425 with
                                              | (env1,goal,opts) ->
                                                  let uu____22441 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22441, opts)))))
                              else
                                (let uu____22443 =
                                   let uu____22450 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22450)  in
                                 [uu____22443])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22487  ->
                                    match uu____22487 with
                                    | (env1,goal,opts) ->
                                        let uu____22503 = check_trivial goal
                                           in
                                        (match uu____22503 with
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
                                                (let uu____22511 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22512 =
                                                   let uu____22513 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22514 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22513 uu____22514
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22511 uu____22512)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22517 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22518 =
                                                   let uu____22519 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22519
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22517 uu____22518)
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
      let uu____22533 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22533 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22540 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22540
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22551 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22551 with
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
            let uu____22584 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____22584 with
            | FStar_Pervasives_Native.Some uu____22587 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____22607 = acc  in
            match uu____22607 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22659 = hd1  in
                     (match uu____22659 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____22673 = unresolved ctx_u  in
                             if uu____22673
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___210_22685 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___210_22685.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___210_22685.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___210_22685.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___210_22685.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___210_22685.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___210_22685.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___210_22685.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___210_22685.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___210_22685.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___210_22685.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___210_22685.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___210_22685.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___210_22685.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___210_22685.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___210_22685.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___210_22685.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___210_22685.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___210_22685.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___210_22685.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___210_22685.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___210_22685.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___210_22685.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___210_22685.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___210_22685.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___210_22685.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___210_22685.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___210_22685.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___210_22685.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___210_22685.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___210_22685.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___210_22685.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___210_22685.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___210_22685.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___210_22685.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___210_22685.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___210_22685.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___210_22685.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___210_22685.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___211_22688 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___211_22688.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___211_22688.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___211_22688.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___211_22688.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___211_22688.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___211_22688.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___211_22688.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___211_22688.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___211_22688.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___211_22688.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___211_22688.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___211_22688.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___211_22688.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___211_22688.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___211_22688.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___211_22688.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___211_22688.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___211_22688.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___211_22688.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___211_22688.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___211_22688.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___211_22688.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___211_22688.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___211_22688.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___211_22688.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___211_22688.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___211_22688.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___211_22688.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___211_22688.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___211_22688.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___211_22688.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___211_22688.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___211_22688.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___211_22688.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___211_22688.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___211_22688.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___211_22688.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___211_22688.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____22691 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22691
                                   then
                                     let uu____22692 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____22693 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____22694 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____22695 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____22692 uu____22693 uu____22694
                                       reason uu____22695
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____22706 =
                                             let uu____22715 =
                                               let uu____22722 =
                                                 let uu____22723 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____22724 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____22725 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____22723 uu____22724
                                                   uu____22725
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____22722, r)
                                                in
                                             [uu____22715]  in
                                           FStar_Errors.add_errors
                                             uu____22706);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___214_22739 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___214_22739.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___214_22739.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___214_22739.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____22742 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____22752  ->
                                               let uu____22753 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____22754 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____22755 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____22753 uu____22754
                                                 reason uu____22755)) env2 g2
                                         true
                                        in
                                     match uu____22742 with
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
          let uu___215_22765 = g  in
          let uu____22766 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___215_22765.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___215_22765.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___215_22765.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____22766
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
        let uu____22816 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____22816 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22825 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____22825
      | (reason,e,ctx_u,r)::uu____22830 ->
          let uu____22849 =
            let uu____22854 =
              let uu____22855 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____22856 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____22855 uu____22856 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____22854)
             in
          FStar_Errors.raise_error uu____22849 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___216_22867 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___216_22867.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___216_22867.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___216_22867.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____22882 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22882 with
      | FStar_Pervasives_Native.Some uu____22888 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22904 = try_teq false env t1 t2  in
        match uu____22904 with
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
        (let uu____22938 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22938
         then
           let uu____22939 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____22940 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22939
             uu____22940
         else ());
        (let uu____22942 =
           let uu____22949 = empty_worklist env  in
           new_t_prob uu____22949 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____22942 with
         | (prob,x,wl) ->
             let g =
               let uu____22962 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____22980  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____22962  in
             ((let uu____23008 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23008
               then
                 let uu____23009 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23010 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23011 =
                   let uu____23012 = FStar_Util.must g  in
                   guard_to_string env uu____23012  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23009 uu____23010 uu____23011
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
        let uu____23046 = check_subtyping env t1 t2  in
        match uu____23046 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23065 =
              let uu____23066 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23066 g  in
            FStar_Pervasives_Native.Some uu____23065
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23084 = check_subtyping env t1 t2  in
        match uu____23084 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23103 =
              let uu____23104 =
                let uu____23105 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23105]  in
              close_guard env uu____23104 g  in
            FStar_Pervasives_Native.Some uu____23103
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23134 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23134
         then
           let uu____23135 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23136 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23135
             uu____23136
         else ());
        (let uu____23138 =
           let uu____23145 = empty_worklist env  in
           new_t_prob uu____23145 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23138 with
         | (prob,x,wl) ->
             let g =
               let uu____23152 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23170  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23152  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23199 =
                      let uu____23200 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23200]  in
                    close_guard env uu____23199 g1  in
                  discharge_guard_nosmt env g2))
  