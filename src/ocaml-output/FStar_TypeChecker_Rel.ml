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
          let uu___146_160 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___146_160.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___146_160.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___146_160.FStar_TypeChecker_Env.implicits)
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
          let uu___147_306 = g  in
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
              (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
              uu____308
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____307;
            FStar_TypeChecker_Env.deferred =
              (uu___147_306.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___147_306.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___147_306.FStar_TypeChecker_Env.implicits)
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
          let uu___148_389 = g  in
          let uu____390 =
            let uu____391 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____391  in
          {
            FStar_TypeChecker_Env.guard_f = uu____390;
            FStar_TypeChecker_Env.deferred =
              (uu___148_389.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___148_389.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___148_389.FStar_TypeChecker_Env.implicits)
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
            let uu___149_555 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___149_555.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___149_555.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___149_555.FStar_TypeChecker_Env.implicits)
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
            let uu___150_615 = g  in
            let uu____616 =
              let uu____617 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____617  in
            {
              FStar_TypeChecker_Env.guard_f = uu____616;
              FStar_TypeChecker_Env.deferred =
                (uu___150_615.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___150_615.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___150_615.FStar_TypeChecker_Env.implicits)
            }
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
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
  wl_implicits: FStar_TypeChecker_Env.implicits }
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
                   (let uu___151_997 = wl  in
                    {
                      attempting = (uu___151_997.attempting);
                      wl_deferred = (uu___151_997.wl_deferred);
                      ctr = (uu___151_997.ctr);
                      defer_ok = (uu___151_997.defer_ok);
                      smt_ok = (uu___151_997.smt_ok);
                      tcenv = (uu___151_997.tcenv);
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
  FStar_Pervasives_Native.tuple2 
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
  | INVARIANT 
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
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___114_1141  ->
    match uu___114_1141 with
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
    fun uu___115_1236  ->
      match uu___115_1236 with
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
    fun uu___116_1270  ->
      match uu___116_1270 with
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
        let uu___152_1410 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___152_1410.wl_deferred);
          ctr = (uu___152_1410.ctr);
          defer_ok = (uu___152_1410.defer_ok);
          smt_ok;
          tcenv = (uu___152_1410.tcenv);
          wl_implicits = (uu___152_1410.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1417 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1417,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___153_1440 = empty_worklist env  in
      let uu____1441 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1441;
        wl_deferred = (uu___153_1440.wl_deferred);
        ctr = (uu___153_1440.ctr);
        defer_ok = (uu___153_1440.defer_ok);
        smt_ok = (uu___153_1440.smt_ok);
        tcenv = (uu___153_1440.tcenv);
        wl_implicits = (uu___153_1440.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___154_1461 = wl  in
        {
          attempting = (uu___154_1461.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___154_1461.ctr);
          defer_ok = (uu___154_1461.defer_ok);
          smt_ok = (uu___154_1461.smt_ok);
          tcenv = (uu___154_1461.tcenv);
          wl_implicits = (uu___154_1461.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___155_1482 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___155_1482.wl_deferred);
        ctr = (uu___155_1482.ctr);
        defer_ok = (uu___155_1482.defer_ok);
        smt_ok = (uu___155_1482.smt_ok);
        tcenv = (uu___155_1482.tcenv);
        wl_implicits = (uu___155_1482.wl_implicits)
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
  fun uu___117_1506  ->
    match uu___117_1506 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1511 .
    'Auu____1511 FStar_TypeChecker_Common.problem ->
      'Auu____1511 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___156_1523 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___156_1523.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___156_1523.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___156_1523.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___156_1523.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___156_1523.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___156_1523.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___156_1523.FStar_TypeChecker_Common.rank)
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
  fun uu___118_1547  ->
    match uu___118_1547 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.TProb _0_17)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.CProb _0_18)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___119_1562  ->
    match uu___119_1562 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___157_1568 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___157_1568.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___157_1568.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___157_1568.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___157_1568.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___157_1568.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___157_1568.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___157_1568.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___157_1568.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___157_1568.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___158_1576 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___158_1576.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___158_1576.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___158_1576.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___158_1576.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___158_1576.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___158_1576.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___158_1576.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___158_1576.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___158_1576.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___120_1588  ->
      match uu___120_1588 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___121_1593  ->
    match uu___121_1593 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___122_1604  ->
    match uu___122_1604 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___123_1617  ->
    match uu___123_1617 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___124_1630  ->
    match uu___124_1630 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___125_1641  ->
    match uu___125_1641 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___126_1656  ->
    match uu___126_1656 with
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
  fun uu___127_1928  ->
    match uu___127_1928 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
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
                          (let uu___159_2551 = wl  in
                           {
                             attempting = (uu___159_2551.attempting);
                             wl_deferred = (uu___159_2551.wl_deferred);
                             ctr = (uu___159_2551.ctr);
                             defer_ok = (uu___159_2551.defer_ok);
                             smt_ok = (uu___159_2551.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___159_2551.wl_implicits)
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
         (fun uu___128_2754  ->
            match uu___128_2754 with
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
        (fun uu___129_2788  ->
           match uu___129_2788 with
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
        (fun uu___130_2822  ->
           match uu___130_2822 with
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
                    let uu___160_2937 = x  in
                    let uu____2938 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___160_2937.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___160_2937.FStar_Syntax_Syntax.index);
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
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                                FStar_Syntax_Syntax.term'
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
                (let uu____3089 = norm_refinement env t12  in
                 match uu____3089 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3106;
                     FStar_Syntax_Syntax.vars = uu____3107;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3133 =
                       let uu____3134 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3135 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3134 uu____3135
                        in
                     failwith uu____3133)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3151 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3151
          | FStar_Syntax_Syntax.Tm_uinst uu____3152 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3189 =
                   let uu____3190 = FStar_Syntax_Subst.compress t1'  in
                   uu____3190.FStar_Syntax_Syntax.n  in
                 match uu____3189 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3207 -> aux true t1'
                 | uu____3214 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3229 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3260 =
                   let uu____3261 = FStar_Syntax_Subst.compress t1'  in
                   uu____3261.FStar_Syntax_Syntax.n  in
                 match uu____3260 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3278 -> aux true t1'
                 | uu____3285 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3300 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3345 =
                   let uu____3346 = FStar_Syntax_Subst.compress t1'  in
                   uu____3346.FStar_Syntax_Syntax.n  in
                 match uu____3345 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3363 -> aux true t1'
                 | uu____3370 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3385 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3400 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3415 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3430 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3445 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3472 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3503 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3524 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3553 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3580 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3617 ->
              let uu____3624 =
                let uu____3625 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3626 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3625 uu____3626
                 in
              failwith uu____3624
          | FStar_Syntax_Syntax.Tm_ascribed uu____3641 ->
              let uu____3668 =
                let uu____3669 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3670 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3669 uu____3670
                 in
              failwith uu____3668
          | FStar_Syntax_Syntax.Tm_delayed uu____3685 ->
              let uu____3710 =
                let uu____3711 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3712 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3711 uu____3712
                 in
              failwith uu____3710
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3727 =
                let uu____3728 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3729 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3728 uu____3729
                 in
              failwith uu____3727
           in
        let uu____3744 = whnf env t1  in aux false uu____3744
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Normalize.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____3790 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3790 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3826 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3826, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3837 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3837 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3862 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3862 with
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
  fun uu____3945  ->
    match uu____3945 with
    | (t_base,refopt) ->
        let uu____3978 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3978 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4018 =
      let uu____4021 =
        let uu____4024 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4047  ->
                  match uu____4047 with | (uu____4054,uu____4055,x) -> x))
           in
        FStar_List.append wl.attempting uu____4024  in
      FStar_List.map (wl_prob_to_string wl) uu____4021  in
    FStar_All.pipe_right uu____4018 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4069 .
    ('Auu____4069,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4080  ->
    match uu____4080 with
    | (uu____4087,c,args) ->
        let uu____4090 = print_ctx_uvar c  in
        let uu____4091 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4090 uu____4091
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4097 = FStar_Syntax_Util.head_and_args t  in
    match uu____4097 with
    | (head1,_args) ->
        let uu____4134 =
          let uu____4135 = FStar_Syntax_Subst.compress head1  in
          uu____4135.FStar_Syntax_Syntax.n  in
        (match uu____4134 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4138 -> true
         | uu____4153 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4159 = FStar_Syntax_Util.head_and_args t  in
    match uu____4159 with
    | (head1,_args) ->
        let uu____4196 =
          let uu____4197 = FStar_Syntax_Subst.compress head1  in
          uu____4197.FStar_Syntax_Syntax.n  in
        (match uu____4196 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4201) -> u
         | uu____4222 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4245 = FStar_Syntax_Util.head_and_args t  in
      match uu____4245 with
      | (head1,args) ->
          let uu____4286 =
            let uu____4287 = FStar_Syntax_Subst.compress head1  in
            uu____4287.FStar_Syntax_Syntax.n  in
          (match uu____4286 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4295)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4338 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___131_4363  ->
                         match uu___131_4363 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4367 =
                               let uu____4368 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4368.FStar_Syntax_Syntax.n  in
                             (match uu____4367 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4372 -> false)
                         | uu____4373 -> true))
                  in
               (match uu____4338 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4395 =
                        FStar_List.collect
                          (fun uu___132_4401  ->
                             match uu___132_4401 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4405 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4405]
                             | uu____4406 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4395 FStar_List.rev  in
                    let uu____4415 =
                      let uu____4422 =
                        let uu____4429 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___133_4443  ->
                                  match uu___133_4443 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4447 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4447]
                                  | uu____4448 -> []))
                           in
                        FStar_All.pipe_right uu____4429 FStar_List.rev  in
                      let uu____4465 =
                        let uu____4468 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4468  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4422 uu____4465
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4415 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4497  ->
                                match uu____4497 with
                                | (x,i) ->
                                    let uu____4508 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4508, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4531  ->
                                match uu____4531 with
                                | (a,i) ->
                                    let uu____4542 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4542, i)) args_sol
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
           | uu____4558 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4578 =
          let uu____4591 =
            let uu____4592 = FStar_Syntax_Subst.compress k  in
            uu____4592.FStar_Syntax_Syntax.n  in
          match uu____4591 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4645 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4645)
              else
                (let uu____4659 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4659 with
                 | (ys',t1,uu____4682) ->
                     let uu____4687 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4687))
          | uu____4728 ->
              let uu____4729 =
                let uu____4740 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4740)  in
              ((ys, t), uu____4729)
           in
        match uu____4578 with
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
                 let uu____4789 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4789 c  in
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
               (let uu____4863 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4863
                then
                  let uu____4864 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4865 = print_ctx_uvar uv  in
                  let uu____4866 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4864 uu____4865 uu____4866
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
             let uu____4872 = p_guard_uvar prob  in
             match uu____4872 with
             | (xs,uv) ->
                 let fail1 uu____4884 =
                   let uu____4885 =
                     let uu____4886 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4887 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4886 uu____4887
                      in
                   failwith uu____4885  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____4937  ->
                           match uu____4937 with
                           | (a,i) ->
                               let uu____4950 =
                                 let uu____4951 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____4951.FStar_Syntax_Syntax.n  in
                               (match uu____4950 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____4969 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____4977 =
                     let uu____4978 = is_flex g  in
                     Prims.op_Negation uu____4978  in
                   if uu____4977
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____4982 = destruct_flex_t g wl  in
                      match uu____4982 with
                      | ((uu____4987,uv1,args),wl1) ->
                          ((let uu____4992 = args_as_binders args  in
                            assign_solution uu____4992 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___161_4994 = wl1  in
                   {
                     attempting = (uu___161_4994.attempting);
                     wl_deferred = (uu___161_4994.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___161_4994.defer_ok);
                     smt_ok = (uu___161_4994.smt_ok);
                     tcenv = (uu___161_4994.tcenv);
                     wl_implicits = (uu___161_4994.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5015 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5015
         then
           let uu____5016 = FStar_Util.string_of_int pid  in
           let uu____5017 =
             let uu____5018 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5018 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5016 uu____5017
         else ());
        commit sol;
        (let uu___162_5025 = wl  in
         {
           attempting = (uu___162_5025.attempting);
           wl_deferred = (uu___162_5025.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___162_5025.defer_ok);
           smt_ok = (uu___162_5025.smt_ok);
           tcenv = (uu___162_5025.tcenv);
           wl_implicits = (uu___162_5025.wl_implicits)
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
             | (uu____5087,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5113 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5113
              in
           (let uu____5119 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5119
            then
              let uu____5120 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5121 =
                let uu____5122 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5122 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5120 uu____5121
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
        let uu____5147 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5147 FStar_Util.set_elements  in
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
      let uu____5181 = occurs uk t  in
      match uu____5181 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5210 =
                 let uu____5211 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5212 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5211 uu____5212
                  in
               FStar_Pervasives_Native.Some uu____5210)
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
            let uu____5301 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5301 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5345 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5393  ->
             match uu____5393 with
             | (x,uu____5403) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5416 = FStar_List.last bs  in
      match uu____5416 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5434) ->
          let uu____5439 =
            FStar_Util.prefix_until
              (fun uu___134_5454  ->
                 match uu___134_5454 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5456 -> false) g
             in
          (match uu____5439 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5469,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5505 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5505 with
        | (pfx,uu____5515) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5527 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5527 with
             | (uu____5534,src',wl1) ->
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
                 | uu____5634 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5635 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5689  ->
                  fun uu____5690  ->
                    match (uu____5689, uu____5690) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5771 =
                          let uu____5772 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5772
                           in
                        if uu____5771
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5797 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5797
                           then
                             let uu____5810 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5810)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5635 with | (isect,uu____5847) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5876 'Auu____5877 .
    (FStar_Syntax_Syntax.bv,'Auu____5876) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5877) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5934  ->
              fun uu____5935  ->
                match (uu____5934, uu____5935) with
                | ((a,uu____5953),(b,uu____5955)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5970 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5970) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6000  ->
           match uu____6000 with
           | (y,uu____6006) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6015 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6015) FStar_Pervasives_Native.tuple2
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
                   let uu____6145 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6145
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6165 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____6208 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6246 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6259 -> false
  
let string_of_option :
  'Auu____6266 .
    ('Auu____6266 -> Prims.string) ->
      'Auu____6266 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___135_6281  ->
      match uu___135_6281 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6287 = f x  in Prims.strcat "Some " uu____6287
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___136_6292  ->
    match uu___136_6292 with
    | MisMatch (d1,d2) ->
        let uu____6303 =
          let uu____6304 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6305 =
            let uu____6306 =
              let uu____6307 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6307 ")"  in
            Prims.strcat ") (" uu____6306  in
          Prims.strcat uu____6304 uu____6305  in
        Prims.strcat "MisMatch (" uu____6303
    | HeadMatch u ->
        let uu____6309 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6309
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___137_6314  ->
    match uu___137_6314 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6329 -> HeadMatch false
  
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
          let uu____6343 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6343 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6354 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6377 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6386 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6414 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6414
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6415 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6416 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6417 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6432 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6445 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6469) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6475,uu____6476) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6518) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6539;
             FStar_Syntax_Syntax.index = uu____6540;
             FStar_Syntax_Syntax.sort = t2;_},uu____6542)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6549 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6550 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6551 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6564 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6571 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6589 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6589
  
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
            let uu____6616 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6616
            then FullMatch
            else
              (let uu____6618 =
                 let uu____6627 =
                   let uu____6630 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6630  in
                 let uu____6631 =
                   let uu____6634 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6634  in
                 (uu____6627, uu____6631)  in
               MisMatch uu____6618)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6640),FStar_Syntax_Syntax.Tm_uinst (g,uu____6642)) ->
            let uu____6651 = head_matches env f g  in
            FStar_All.pipe_right uu____6651 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6654 = FStar_Const.eq_const c d  in
            if uu____6654
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6661),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6663)) ->
            let uu____6704 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6704
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6711),FStar_Syntax_Syntax.Tm_refine (y,uu____6713)) ->
            let uu____6722 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6722 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6724),uu____6725) ->
            let uu____6730 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6730 head_match
        | (uu____6731,FStar_Syntax_Syntax.Tm_refine (x,uu____6733)) ->
            let uu____6738 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6738 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6739,FStar_Syntax_Syntax.Tm_type
           uu____6740) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6741,FStar_Syntax_Syntax.Tm_arrow uu____6742) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6768),FStar_Syntax_Syntax.Tm_app (head',uu____6770))
            ->
            let uu____6811 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6811 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6813),uu____6814) ->
            let uu____6835 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6835 head_match
        | (uu____6836,FStar_Syntax_Syntax.Tm_app (head1,uu____6838)) ->
            let uu____6859 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6859 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6860,FStar_Syntax_Syntax.Tm_let
           uu____6861) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6886,FStar_Syntax_Syntax.Tm_match uu____6887) ->
            HeadMatch true
        | uu____6932 ->
            let uu____6937 =
              let uu____6946 = delta_depth_of_term env t11  in
              let uu____6949 = delta_depth_of_term env t21  in
              (uu____6946, uu____6949)  in
            MisMatch uu____6937
  
let head_matches_delta :
  'Auu____6966 .
    FStar_TypeChecker_Env.env ->
      'Auu____6966 ->
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
            let head1 = FStar_Syntax_Util.head_of t  in
            (let uu____7015 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7015
             then
               let uu____7016 = FStar_Syntax_Print.term_to_string t  in
               let uu____7017 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7016 uu____7017
             else ());
            (let uu____7019 =
               let uu____7020 = FStar_Syntax_Util.un_uinst head1  in
               uu____7020.FStar_Syntax_Syntax.n  in
             match uu____7019 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7026 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7026 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7040 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7040
                        then
                          let uu____7041 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7041
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7043 ->
                      let t' =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Normalize.Weak;
                          FStar_TypeChecker_Normalize.HNF;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding] env t
                         in
                      ((let uu____7054 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7054
                        then
                          let uu____7055 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7056 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7055
                            uu____7056
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7058 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____7196 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7196
             then
               let uu____7197 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7198 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7199 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7197
                 uu____7198 uu____7199
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7223 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                       FStar_TypeChecker_Normalize.Weak;
                       FStar_TypeChecker_Normalize.HNF] env t11
                      in
                   (t1', t21)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                        FStar_TypeChecker_Normalize.Weak;
                        FStar_TypeChecker_Normalize.HNF] env t21
                       in
                    (t11, t2'))
                  in
               match uu____7223 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7268 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7268 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                       FStar_TypeChecker_Normalize.Weak;
                       FStar_TypeChecker_Normalize.HNF] env t11
                      in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                       FStar_TypeChecker_Normalize.Weak;
                       FStar_TypeChecker_Normalize.HNF] env t21
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
                 ((i > (Prims.parse_int "0")) || (j > (Prims.parse_int "0")))
                   && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____7300),uu____7301)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7319 =
                      let uu____7328 = maybe_inline t11  in
                      let uu____7331 = maybe_inline t21  in
                      (uu____7328, uu____7331)  in
                    match uu____7319 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
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
                 (uu____7368,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7369))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7387 =
                      let uu____7396 = maybe_inline t11  in
                      let uu____7399 = maybe_inline t21  in
                      (uu____7396, uu____7399)  in
                    match uu____7387 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
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
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____7448 -> fail1 n_delta r t11 t21
             | uu____7457 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7470 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7470
           then
             let uu____7471 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7472 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7473 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7480 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7498 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7498
                    (fun uu____7532  ->
                       match uu____7532 with
                       | (t11,t21) ->
                           let uu____7539 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7540 =
                             let uu____7541 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7541  in
                           Prims.strcat uu____7539 uu____7540))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7471 uu____7472 uu____7473 uu____7480
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7553 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7553 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___138_7566  ->
    match uu___138_7566 with
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
      let uu___163_7603 = p  in
      let uu____7606 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7607 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___163_7603.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7606;
        FStar_TypeChecker_Common.relation =
          (uu___163_7603.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7607;
        FStar_TypeChecker_Common.element =
          (uu___163_7603.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___163_7603.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___163_7603.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___163_7603.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___163_7603.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___163_7603.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7621 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7621
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7626 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7648 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7648 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7656 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7656 with
           | (lh,lhs_args) ->
               let uu____7697 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7697 with
                | (rh,rhs_args) ->
                    let uu____7738 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7751,FStar_Syntax_Syntax.Tm_uvar uu____7752)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7833 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7856,uu____7857)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_7875 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_7875.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_7875.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_7875.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_7875.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_7875.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_7875.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_7875.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_7875.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_7875.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7878,FStar_Syntax_Syntax.Tm_uvar uu____7879)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_7897 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_7897.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_7897.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_7897.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_7897.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_7897.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_7897.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_7897.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_7897.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_7897.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7900,FStar_Syntax_Syntax.Tm_arrow uu____7901)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___165_7931 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___165_7931.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___165_7931.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___165_7931.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___165_7931.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___165_7931.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___165_7931.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___165_7931.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___165_7931.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___165_7931.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7934,FStar_Syntax_Syntax.Tm_type uu____7935)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___165_7953 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___165_7953.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___165_7953.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___165_7953.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___165_7953.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___165_7953.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___165_7953.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___165_7953.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___165_7953.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___165_7953.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7956,FStar_Syntax_Syntax.Tm_uvar uu____7957)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___165_7975 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___165_7975.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___165_7975.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___165_7975.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___165_7975.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___165_7975.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___165_7975.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___165_7975.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___165_7975.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___165_7975.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7978,FStar_Syntax_Syntax.Tm_uvar uu____7979)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7996,uu____7997)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8014,FStar_Syntax_Syntax.Tm_uvar uu____8015)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8032,uu____8033) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7738 with
                     | (rank,tp1) ->
                         let uu____8046 =
                           FStar_All.pipe_right
                             (let uu___166_8050 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___166_8050.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___166_8050.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___166_8050.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___166_8050.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___166_8050.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___166_8050.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___166_8050.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___166_8050.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___166_8050.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8046))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8056 =
            FStar_All.pipe_right
              (let uu___167_8060 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___167_8060.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___167_8060.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___167_8060.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___167_8060.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___167_8060.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___167_8060.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___167_8060.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___167_8060.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___167_8060.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8056)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8121 probs =
      match uu____8121 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8202 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8223 = rank wl.tcenv hd1  in
               (match uu____8223 with
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
                      (let uu____8282 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8286 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8286)
                          in
                       if uu____8282
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
          let uu____8354 = FStar_Syntax_Util.head_and_args t  in
          match uu____8354 with
          | (hd1,uu____8370) ->
              let uu____8391 =
                let uu____8392 = FStar_Syntax_Subst.compress hd1  in
                uu____8392.FStar_Syntax_Syntax.n  in
              (match uu____8391 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8396) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8430  ->
                           match uu____8430 with
                           | (y,uu____8436) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8450  ->
                                       match uu____8450 with
                                       | (x,uu____8456) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8457 -> false)
           in
        let uu____8458 = rank tcenv p  in
        match uu____8458 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8465 -> true
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
  | UFailed of Prims.string 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8492 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8506 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8520 -> false
  
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
                        let uu____8572 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8572 with
                        | (k,uu____8578) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8588 -> false)))
            | uu____8589 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8641 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8647 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8647 = (Prims.parse_int "0")))
                           in
                        if uu____8641 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8663 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8669 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8669 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8663)
               in
            let uu____8670 = filter1 u12  in
            let uu____8673 = filter1 u22  in (uu____8670, uu____8673)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8702 = filter_out_common_univs us1 us2  in
                (match uu____8702 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8761 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8761 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8764 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8774 =
                          let uu____8775 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8776 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8775
                            uu____8776
                           in
                        UFailed uu____8774))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8800 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8800 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8826 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8826 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8829 ->
                let uu____8834 =
                  let uu____8835 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8836 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8835
                    uu____8836 msg
                   in
                UFailed uu____8834
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8837,uu____8838) ->
              let uu____8839 =
                let uu____8840 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8841 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8840 uu____8841
                 in
              failwith uu____8839
          | (FStar_Syntax_Syntax.U_unknown ,uu____8842) ->
              let uu____8843 =
                let uu____8844 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8845 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8844 uu____8845
                 in
              failwith uu____8843
          | (uu____8846,FStar_Syntax_Syntax.U_bvar uu____8847) ->
              let uu____8848 =
                let uu____8849 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8850 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8849 uu____8850
                 in
              failwith uu____8848
          | (uu____8851,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8852 =
                let uu____8853 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8854 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8853 uu____8854
                 in
              failwith uu____8852
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8878 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8878
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8892 = occurs_univ v1 u3  in
              if uu____8892
              then
                let uu____8893 =
                  let uu____8894 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8895 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8894 uu____8895
                   in
                try_umax_components u11 u21 uu____8893
              else
                (let uu____8897 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8897)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8909 = occurs_univ v1 u3  in
              if uu____8909
              then
                let uu____8910 =
                  let uu____8911 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8912 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8911 uu____8912
                   in
                try_umax_components u11 u21 uu____8910
              else
                (let uu____8914 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8914)
          | (FStar_Syntax_Syntax.U_max uu____8915,uu____8916) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8922 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8922
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8924,FStar_Syntax_Syntax.U_max uu____8925) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8931 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8931
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8933,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8934,FStar_Syntax_Syntax.U_name
             uu____8935) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8936) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8937) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8938,FStar_Syntax_Syntax.U_succ
             uu____8939) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8940,FStar_Syntax_Syntax.U_zero
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
      let uu____9040 = bc1  in
      match uu____9040 with
      | (bs1,mk_cod1) ->
          let uu____9084 = bc2  in
          (match uu____9084 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9195 = aux xs ys  in
                     (match uu____9195 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9278 =
                       let uu____9285 = mk_cod1 xs  in ([], uu____9285)  in
                     let uu____9288 =
                       let uu____9295 = mk_cod2 ys  in ([], uu____9295)  in
                     (uu____9278, uu____9288)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  FStar_Syntax_Util.mk_has_type t11 t t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9365 =
                    let uu____9366 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9366 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9365
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9371 = has_type_guard t1 t2  in (uu____9371, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9372 = has_type_guard t2 t1  in (uu____9372, wl)
  
let is_flex_pat :
  'Auu____9381 'Auu____9382 'Auu____9383 .
    ('Auu____9381,'Auu____9382,'Auu____9383 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___139_9396  ->
    match uu___139_9396 with
    | (uu____9405,uu____9406,[]) -> true
    | uu____9409 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9440 = f  in
      match uu____9440 with
      | (uu____9447,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9448;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9449;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9452;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9453;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9454;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9506  ->
                 match uu____9506 with
                 | (y,uu____9512) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9634 =
                  let uu____9647 =
                    let uu____9650 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9650  in
                  ((FStar_List.rev pat_binders), uu____9647)  in
                FStar_Pervasives_Native.Some uu____9634
            | (uu____9677,[]) ->
                let uu____9700 =
                  let uu____9713 =
                    let uu____9716 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9716  in
                  ((FStar_List.rev pat_binders), uu____9713)  in
                FStar_Pervasives_Native.Some uu____9700
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9781 =
                  let uu____9782 = FStar_Syntax_Subst.compress a  in
                  uu____9782.FStar_Syntax_Syntax.n  in
                (match uu____9781 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9800 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9800
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___168_9821 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___168_9821.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___168_9821.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9825 =
                            let uu____9826 =
                              let uu____9833 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9833)  in
                            FStar_Syntax_Syntax.NT uu____9826  in
                          [uu____9825]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___169_9845 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___169_9845.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___169_9845.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9846 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9874 =
                  let uu____9887 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9887  in
                (match uu____9874 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9950 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9977 ->
               let uu____9978 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9978 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10254 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10254
       then
         let uu____10255 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10255
       else ());
      (let uu____10257 = next_prob probs  in
       match uu____10257 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___170_10284 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___170_10284.wl_deferred);
               ctr = (uu___170_10284.ctr);
               defer_ok = (uu___170_10284.defer_ok);
               smt_ok = (uu___170_10284.smt_ok);
               tcenv = (uu___170_10284.tcenv);
               wl_implicits = (uu___170_10284.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10291 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10291
                then
                  let uu____10292 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10292
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
                          (let uu___171_10297 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___171_10297.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___171_10297.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___171_10297.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___171_10297.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___171_10297.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___171_10297.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___171_10297.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___171_10297.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___171_10297.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10319 ->
                let uu____10328 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10387  ->
                          match uu____10387 with
                          | (c,uu____10395,uu____10396) -> c < probs.ctr))
                   in
                (match uu____10328 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10437 =
                            let uu____10442 =
                              FStar_List.map
                                (fun uu____10457  ->
                                   match uu____10457 with
                                   | (uu____10468,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10442, (probs.wl_implicits))  in
                          Success uu____10437
                      | uu____10471 ->
                          let uu____10480 =
                            let uu___172_10481 = probs  in
                            let uu____10482 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10501  ->
                                      match uu____10501 with
                                      | (uu____10508,uu____10509,y) -> y))
                               in
                            {
                              attempting = uu____10482;
                              wl_deferred = rest;
                              ctr = (uu___172_10481.ctr);
                              defer_ok = (uu___172_10481.defer_ok);
                              smt_ok = (uu___172_10481.smt_ok);
                              tcenv = (uu___172_10481.tcenv);
                              wl_implicits = (uu___172_10481.wl_implicits)
                            }  in
                          solve env uu____10480))))

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
            let uu____10516 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10516 with
            | USolved wl1 ->
                let uu____10518 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10518
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
                  let uu____10570 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10570 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10573 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10585;
                  FStar_Syntax_Syntax.vars = uu____10586;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10589;
                  FStar_Syntax_Syntax.vars = uu____10590;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10602,uu____10603) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10610,FStar_Syntax_Syntax.Tm_uinst uu____10611) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10618 -> USolved wl

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
            ((let uu____10628 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10628
              then
                let uu____10629 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10629 msg
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
              let uu____10714 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10714 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10766 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10766
               then
                 let uu____10767 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10768 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10767
                   uu____10768
               else ());
              (let uu____10770 = head_matches_delta env1 () t1 t2  in
               match uu____10770 with
               | (mr,ts1) ->
                   (match mr with
                    | HeadMatch (true ) ->
                        let uu____10815 = eq_prob t1 t2 wl2  in
                        (match uu____10815 with | (p,wl3) -> (t1, [p], wl3))
                    | MisMatch uu____10836 ->
                        let uu____10845 = eq_prob t1 t2 wl2  in
                        (match uu____10845 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch (false ) ->
                        let uu____10892 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10907 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10908 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10907, uu____10908)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10913 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10914 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10913, uu____10914)
                           in
                        (match uu____10892 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10945 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10945 with
                               | (t1_hd,t1_args) ->
                                   let uu____10984 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10984 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____11038 =
                                             let uu____11045 =
                                               let uu____11054 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____11054 :: t1_args  in
                                             let uu____11067 =
                                               let uu____11074 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____11074 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____11115  ->
                                                  fun uu____11116  ->
                                                    fun uu____11117  ->
                                                      match (uu____11115,
                                                              uu____11116,
                                                              uu____11117)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____11159),
                                                         (a2,uu____11161)) ->
                                                          let uu____11186 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____11186
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____11045
                                               uu____11067
                                              in
                                           match uu____11038 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___173_11212 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___173_11212.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___173_11212.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11228 =
                                                 solve env1 wl'  in
                                               (match uu____11228 with
                                                | Success (uu____11231,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___174_11235 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___174_11235.attempting);
                                                           wl_deferred =
                                                             (uu___174_11235.wl_deferred);
                                                           ctr =
                                                             (uu___174_11235.ctr);
                                                           defer_ok =
                                                             (uu___174_11235.defer_ok);
                                                           smt_ok =
                                                             (uu___174_11235.smt_ok);
                                                           tcenv =
                                                             (uu___174_11235.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11244 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11276 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11276 with
                               | (t1_base,p1_opt) ->
                                   let uu____11323 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11323 with
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
                                              let uu____11460 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____11460
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
                                              let uu____11490 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11490
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
                                              let uu____11520 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11520
                                          | uu____11523 -> t_base  in
                                        let uu____11540 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11540 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11554 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11554, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11561 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11561 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11608 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11608 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11655 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11655
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
                             let uu____11679 = combine t11 t21 wl2  in
                             (match uu____11679 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11712 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11712
                                    then
                                      let uu____11713 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11713
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11752 ts1 =
              match uu____11752 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11815 = pairwise out t wl2  in
                       (match uu____11815 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11851 =
              let uu____11862 = FStar_List.hd ts  in (uu____11862, [], wl1)
               in
            let uu____11871 = FStar_List.tl ts  in
            aux uu____11851 uu____11871  in
          let uu____11878 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11878 with
          | (this_flex,this_rigid) ->
              let uu____11890 =
                let uu____11891 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11891.FStar_Syntax_Syntax.n  in
              (match uu____11890 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11912 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11912
                   then
                     let uu____11913 = destruct_flex_t this_flex wl  in
                     (match uu____11913 with
                      | (flex,wl1) ->
                          let uu____11920 = quasi_pattern env flex  in
                          (match uu____11920 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11938 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11938
                                 then
                                   let uu____11939 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11939
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
                             ((let uu___175_11944 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___175_11944.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___175_11944.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___175_11944.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___175_11944.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___175_11944.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___175_11944.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___175_11944.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___175_11944.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___175_11944.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11945 ->
                   ((let uu____11947 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11947
                     then
                       let uu____11948 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11948
                     else ());
                    (let uu____11950 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11950 with
                     | (u,_args) ->
                         let uu____11987 =
                           let uu____11988 = FStar_Syntax_Subst.compress u
                              in
                           uu____11988.FStar_Syntax_Syntax.n  in
                         (match uu____11987 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____12019 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____12019 with
                                | (u',uu____12035) ->
                                    let uu____12056 =
                                      let uu____12057 = whnf env u'  in
                                      uu____12057.FStar_Syntax_Syntax.n  in
                                    (match uu____12056 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____12082 -> false)
                                 in
                              let uu____12083 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___140_12106  ->
                                        match uu___140_12106 with
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
                                             | uu____12115 -> false)
                                        | uu____12118 -> false))
                                 in
                              (match uu____12083 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____12132 = whnf env this_rigid
                                        in
                                     let uu____12133 =
                                       FStar_List.collect
                                         (fun uu___141_12139  ->
                                            match uu___141_12139 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____12145 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____12145]
                                            | uu____12147 -> []) bounds_probs
                                        in
                                     uu____12132 :: uu____12133  in
                                   let uu____12148 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____12148 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____12179 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____12194 =
                                              let uu____12195 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____12195.FStar_Syntax_Syntax.n
                                               in
                                            match uu____12194 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____12207 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____12207)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____12216 -> bound  in
                                          let uu____12217 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____12217)  in
                                        (match uu____12179 with
                                         | (bound_typ,(eq_prob,wl')) ->
                                             ((let uu____12245 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____12245
                                               then
                                                 let wl'1 =
                                                   let uu___176_12247 = wl1
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___176_12247.wl_deferred);
                                                     ctr =
                                                       (uu___176_12247.ctr);
                                                     defer_ok =
                                                       (uu___176_12247.defer_ok);
                                                     smt_ok =
                                                       (uu___176_12247.smt_ok);
                                                     tcenv =
                                                       (uu___176_12247.tcenv);
                                                     wl_implicits =
                                                       (uu___176_12247.wl_implicits)
                                                   }  in
                                                 let uu____12248 =
                                                   wl_to_string wl'1  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____12248
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____12251 =
                                                 solve_t env eq_prob
                                                   (let uu___177_12253 = wl'
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___177_12253.wl_deferred);
                                                      ctr =
                                                        (uu___177_12253.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___177_12253.smt_ok);
                                                      tcenv =
                                                        (uu___177_12253.tcenv);
                                                      wl_implicits =
                                                        (uu___177_12253.wl_implicits)
                                                    })
                                                  in
                                               match uu____12251 with
                                               | Success uu____12254 ->
                                                   let wl2 =
                                                     let uu___178_12260 = wl'
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___178_12260.wl_deferred);
                                                       ctr =
                                                         (uu___178_12260.ctr);
                                                       defer_ok =
                                                         (uu___178_12260.defer_ok);
                                                       smt_ok =
                                                         (uu___178_12260.smt_ok);
                                                       tcenv =
                                                         (uu___178_12260.tcenv);
                                                       wl_implicits =
                                                         (uu___178_12260.wl_implicits)
                                                     }  in
                                                   let wl3 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl2
                                                      in
                                                   let uu____12264 =
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
                                                    (let uu____12276 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12276
                                                     then
                                                       let uu____12277 =
                                                         let uu____12278 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12278
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12277
                                                     else ());
                                                    (let uu____12284 =
                                                       let uu____12299 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12299)
                                                        in
                                                     match uu____12284 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12321))
                                                         ->
                                                         let uu____12346 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12346
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
                                                         let uu____12385 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12385
                                                          with
                                                          | (eq_prob1,wl2) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl2 tp x
                                                                  phi
                                                                 in
                                                              let wl3 =
                                                                let uu____12402
                                                                  =
                                                                  let uu____12407
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12407
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12402
                                                                  [] wl2
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl3))
                                                     | uu____12412 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12427 when flip ->
                              let uu____12428 =
                                let uu____12429 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12430 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12429 uu____12430
                                 in
                              failwith uu____12428
                          | uu____12431 ->
                              let uu____12432 =
                                let uu____12433 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12434 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12433 uu____12434
                                 in
                              failwith uu____12432))))

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
                      (fun uu____12462  ->
                         match uu____12462 with
                         | (x,i) ->
                             let uu____12473 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12473, i)) bs_lhs
                     in
                  let uu____12474 = lhs  in
                  match uu____12474 with
                  | (uu____12475,u_lhs,uu____12477) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12590 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12600 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12600, univ)
                             in
                          match uu____12590 with
                          | (k,univ) ->
                              let uu____12613 =
                                let uu____12620 =
                                  let uu____12623 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12623
                                   in
                                copy_uvar u_lhs uu____12620 wl2  in
                              (match uu____12613 with
                               | (uu____12636,u,wl3) ->
                                   let uu____12639 =
                                     let uu____12642 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12642
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12639, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12678 =
                              let uu____12691 =
                                let uu____12700 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12700 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12746  ->
                                   fun uu____12747  ->
                                     match (uu____12746, uu____12747) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12838 =
                                           let uu____12845 =
                                             let uu____12848 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12848
                                              in
                                           copy_uvar u_lhs uu____12845 wl2
                                            in
                                         (match uu____12838 with
                                          | (uu____12871,t_a,wl3) ->
                                              let uu____12874 =
                                                let uu____12881 =
                                                  let uu____12884 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12884
                                                   in
                                                copy_uvar u_lhs uu____12881
                                                  wl3
                                                 in
                                              (match uu____12874 with
                                               | (uu____12899,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12691
                                ([], wl1)
                               in
                            (match uu____12678 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___179_12960 = ct  in
                                   let uu____12961 =
                                     let uu____12964 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12964
                                      in
                                   let uu____12979 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___179_12960.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___179_12960.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12961;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12979;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___179_12960.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___180_12997 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___180_12997.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___180_12997.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13000 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13000 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13054 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13054 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13071 =
                                          let uu____13076 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13076)  in
                                        TERM uu____13071  in
                                      let uu____13077 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13077 with
                                       | (sub_prob,wl3) ->
                                           let uu____13088 =
                                             let uu____13089 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13089
                                              in
                                           solve env uu____13088))
                             | (x,imp)::formals2 ->
                                 let uu____13103 =
                                   let uu____13110 =
                                     let uu____13113 =
                                       let uu____13116 =
                                         let uu____13117 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____13117
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____13116
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____13113
                                      in
                                   copy_uvar u_lhs uu____13110 wl1  in
                                 (match uu____13103 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____13141 =
                                          let uu____13144 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13144
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13141 t_y
                                         in
                                      let uu____13145 =
                                        let uu____13148 =
                                          let uu____13151 =
                                            let uu____13152 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13152, imp)  in
                                          [uu____13151]  in
                                        FStar_List.append bs_terms
                                          uu____13148
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13145 formals2 wl2)
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
              (let uu____13194 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13194
               then
                 let uu____13195 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13196 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13195 (rel_to_string (p_rel orig)) uu____13196
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13301 = rhs wl1 scope env1 subst1  in
                     (match uu____13301 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13321 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13321
                            then
                              let uu____13322 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13322
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___181_13376 = hd1  in
                       let uu____13377 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___181_13376.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___181_13376.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13377
                       }  in
                     let hd21 =
                       let uu___182_13381 = hd2  in
                       let uu____13382 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___182_13381.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___182_13381.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13382
                       }  in
                     let uu____13385 =
                       let uu____13390 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13390
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13385 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13409 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13409
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13413 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13413 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13468 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13468
                                  in
                               ((let uu____13480 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13480
                                 then
                                   let uu____13481 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13482 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13481
                                     uu____13482
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13509 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13538 = aux wl [] env [] bs1 bs2  in
               match uu____13538 with
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
        (let uu____13589 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13589 wl)

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
              let uu____13603 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13603 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13633 = lhs1  in
              match uu____13633 with
              | (uu____13636,ctx_u,uu____13638) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13644 ->
                        let uu____13645 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13645 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13692 = quasi_pattern env1 lhs1  in
              match uu____13692 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13722) ->
                  let uu____13727 = lhs1  in
                  (match uu____13727 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13741 = occurs_check ctx_u rhs1  in
                       (match uu____13741 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13783 =
                                let uu____13790 =
                                  let uu____13791 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13791
                                   in
                                FStar_Util.Inl uu____13790  in
                              (uu____13783, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13811 =
                                 let uu____13812 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13812  in
                               if uu____13811
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13832 =
                                    let uu____13839 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13839  in
                                  let uu____13844 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13832, uu____13844)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13906  ->
                     match uu____13906 with
                     | (x,i) ->
                         let uu____13917 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13917, i)) bs_lhs
                 in
              let uu____13918 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13918 with
              | (rhs_hd,args) ->
                  let uu____13955 = FStar_Util.prefix args  in
                  (match uu____13955 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14013 = lhs1  in
                       (match uu____14013 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14017 =
                              let uu____14028 =
                                let uu____14035 =
                                  let uu____14038 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14038
                                   in
                                copy_uvar u_lhs uu____14035 wl1  in
                              match uu____14028 with
                              | (uu____14059,t_last_arg,wl2) ->
                                  let uu____14062 =
                                    let uu____14069 =
                                      let uu____14072 =
                                        let uu____14079 =
                                          let uu____14086 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____14086]  in
                                        FStar_List.append bs_lhs uu____14079
                                         in
                                      let uu____14103 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____14072
                                        uu____14103
                                       in
                                    copy_uvar u_lhs uu____14069 wl2  in
                                  (match uu____14062 with
                                   | (uu____14116,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14122 =
                                         let uu____14129 =
                                           let uu____14132 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____14132
                                            in
                                         copy_uvar u_lhs uu____14129 wl3  in
                                       (match uu____14122 with
                                        | (uu____14145,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14017 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14169 =
                                     let uu____14170 =
                                       let uu____14175 =
                                         let uu____14176 =
                                           let uu____14179 =
                                             let uu____14184 =
                                               let uu____14185 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14185]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14184
                                              in
                                           uu____14179
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14176
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14175)  in
                                     TERM uu____14170  in
                                   [uu____14169]  in
                                 let uu____14206 =
                                   let uu____14213 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14213 with
                                   | (p1,wl3) ->
                                       let uu____14230 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14230 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14206 with
                                  | (sub_probs,wl3) ->
                                      let uu____14257 =
                                        let uu____14258 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14258  in
                                      solve env1 uu____14257))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14291 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14291 with
                | (uu____14306,args) ->
                    (match args with | [] -> false | uu____14334 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14349 =
                  let uu____14350 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14350.FStar_Syntax_Syntax.n  in
                match uu____14349 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14353 -> true
                | uu____14366 -> false  in
              let uu____14367 = quasi_pattern env1 lhs1  in
              match uu____14367 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14378 =
                    let uu____14379 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14379
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14378
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14386 = is_app rhs1  in
                  if uu____14386
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14388 = is_arrow rhs1  in
                     if uu____14388
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14390 =
                          let uu____14391 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14391
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14390))
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
                let uu____14394 = lhs  in
                (match uu____14394 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14398 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14398 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14413 =
                              let uu____14416 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14416
                               in
                            FStar_All.pipe_right uu____14413
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14431 = occurs_check ctx_uv rhs1  in
                          (match uu____14431 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14453 =
                                   let uu____14454 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14454
                                    in
                                 giveup_or_defer env orig wl uu____14453
                               else
                                 (let uu____14456 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14456
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14461 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14461
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14463 =
                                         let uu____14464 =
                                           names_to_string1 fvs2  in
                                         let uu____14465 =
                                           names_to_string1 fvs1  in
                                         let uu____14466 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14464 uu____14465
                                           uu____14466
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14463)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14472 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14476 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14476 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14499 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14499
                             | (FStar_Util.Inl msg,uu____14501) ->
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
                  (let uu____14530 =
                     let uu____14547 = quasi_pattern env lhs  in
                     let uu____14554 = quasi_pattern env rhs  in
                     (uu____14547, uu____14554)  in
                   match uu____14530 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14597 = lhs  in
                       (match uu____14597 with
                        | ({ FStar_Syntax_Syntax.n = uu____14598;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14600;_},u_lhs,uu____14602)
                            ->
                            let uu____14605 = rhs  in
                            (match uu____14605 with
                             | (uu____14606,u_rhs,uu____14608) ->
                                 let uu____14609 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14609
                                 then
                                   let uu____14610 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14610
                                 else
                                   (let uu____14612 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14612 with
                                    | (sub_prob,wl1) ->
                                        let uu____14623 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14623 with
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
                                             let uu____14651 =
                                               let uu____14658 =
                                                 let uu____14661 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14661
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
                                                 uu____14658
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14651 with
                                              | (uu____14664,w,wl2) ->
                                                  let w_app =
                                                    let uu____14670 =
                                                      let uu____14675 =
                                                        FStar_List.map
                                                          (fun uu____14684 
                                                             ->
                                                             match uu____14684
                                                             with
                                                             | (z,uu____14690)
                                                                 ->
                                                                 let uu____14691
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14691)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14675
                                                       in
                                                    uu____14670
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14695 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14695
                                                    then
                                                      let uu____14696 =
                                                        let uu____14699 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14700 =
                                                          let uu____14703 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14704 =
                                                            let uu____14707 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14708 =
                                                              let uu____14711
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14716
                                                                =
                                                                let uu____14719
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14724
                                                                  =
                                                                  let uu____14727
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14727]
                                                                   in
                                                                uu____14719
                                                                  ::
                                                                  uu____14724
                                                                 in
                                                              uu____14711 ::
                                                                uu____14716
                                                               in
                                                            uu____14707 ::
                                                              uu____14708
                                                             in
                                                          uu____14703 ::
                                                            uu____14704
                                                           in
                                                        uu____14699 ::
                                                          uu____14700
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14696
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14733 =
                                                          let uu____14738 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14738)
                                                           in
                                                        TERM uu____14733  in
                                                      let uu____14739 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14739
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14744 =
                                                             let uu____14749
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
                                                               uu____14749)
                                                              in
                                                           TERM uu____14744
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14750 =
                                                      let uu____14751 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14751
                                                       in
                                                    solve env uu____14750)))))))
                   | uu____14752 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14816 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14816
            then
              let uu____14817 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14818 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14819 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14820 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14817 uu____14818 uu____14819 uu____14820
            else ());
           (let uu____14824 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14824
            then
              let uu____14825 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14826 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14827 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14828 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14825 uu____14826 uu____14827 uu____14828
            else ());
           (let uu____14830 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14830 with
            | (head1,args1) ->
                let uu____14867 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14867 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____14921 =
                         let uu____14922 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14923 = args_to_string args1  in
                         let uu____14924 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____14925 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____14922 uu____14923 uu____14924 uu____14925
                          in
                       giveup env1 uu____14921 orig
                     else
                       (let uu____14927 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____14934 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____14934 = FStar_Syntax_Util.Equal)
                           in
                        if uu____14927
                        then
                          let uu____14935 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____14935 with
                          | USolved wl2 ->
                              let uu____14937 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____14937
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____14941 = base_and_refinement env1 t1  in
                           match uu____14941 with
                           | (base1,refinement1) ->
                               let uu____14966 = base_and_refinement env1 t2
                                  in
                               (match uu____14966 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15023 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15023 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15027 =
                                                FStar_List.fold_right2
                                                  (fun uu____15060  ->
                                                     fun uu____15061  ->
                                                       fun uu____15062  ->
                                                         match (uu____15060,
                                                                 uu____15061,
                                                                 uu____15062)
                                                         with
                                                         | ((a,uu____15098),
                                                            (a',uu____15100),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15121
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15121
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15027 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15149 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15149
                                                     then
                                                       let uu____15150 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15150
                                                     else ());
                                                    (let formula =
                                                       let uu____15155 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15155
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     solve env1
                                                       (attempt subprobs wl4)))))
                                     | uu____15163 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___183_15203 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___183_15203.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___183_15203.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___183_15203.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___183_15203.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___183_15203.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___183_15203.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___183_15203.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___183_15203.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15241 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15241
            then
              let uu____15242 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15243 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15244 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15245 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15242 uu____15243 uu____15244 uu____15245
            else ());
           (let uu____15247 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15247 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15278,uu____15279) ->
                     let rec may_relate head3 =
                       let uu____15306 =
                         let uu____15307 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15307.FStar_Syntax_Syntax.n  in
                       match uu____15306 with
                       | FStar_Syntax_Syntax.Tm_name uu____15310 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15311 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15334;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15335;
                             FStar_Syntax_Syntax.fv_qual = uu____15336;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15339;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15340;
                             FStar_Syntax_Syntax.fv_qual = uu____15341;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15345,uu____15346) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15388) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15394) ->
                           may_relate t
                       | uu____15399 -> false  in
                     let uu____15400 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15400
                     then
                       let uu____15401 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15401 with
                        | (guard,wl2) ->
                            let uu____15408 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15408)
                     else
                       (let uu____15410 =
                          let uu____15411 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15412 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15411 uu____15412
                           in
                        giveup env1 uu____15410 orig)
                 | (uu____15413,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___184_15427 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_15427.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___184_15427.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___184_15427.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_15427.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___184_15427.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_15427.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_15427.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_15427.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15451 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15451
          then
            let uu____15452 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15452
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15457 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15457
              then
                let uu____15458 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15459 =
                  let uu____15460 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15461 =
                    let uu____15462 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15462  in
                  Prims.strcat uu____15460 uu____15461  in
                let uu____15463 =
                  let uu____15464 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15465 =
                    let uu____15466 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15466  in
                  Prims.strcat uu____15464 uu____15465  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15458
                  uu____15459 uu____15463
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15469,uu____15470) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15495,FStar_Syntax_Syntax.Tm_delayed uu____15496) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15521,uu____15522) ->
                  let uu____15549 =
                    let uu___185_15550 = problem  in
                    let uu____15551 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___185_15550.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15551;
                      FStar_TypeChecker_Common.relation =
                        (uu___185_15550.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___185_15550.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___185_15550.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___185_15550.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___185_15550.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___185_15550.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___185_15550.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___185_15550.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15549 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15552,uu____15553) ->
                  let uu____15560 =
                    let uu___186_15561 = problem  in
                    let uu____15562 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___186_15561.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15562;
                      FStar_TypeChecker_Common.relation =
                        (uu___186_15561.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___186_15561.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___186_15561.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___186_15561.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___186_15561.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___186_15561.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___186_15561.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___186_15561.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15560 wl
              | (uu____15563,FStar_Syntax_Syntax.Tm_ascribed uu____15564) ->
                  let uu____15591 =
                    let uu___187_15592 = problem  in
                    let uu____15593 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___187_15592.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___187_15592.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___187_15592.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15593;
                      FStar_TypeChecker_Common.element =
                        (uu___187_15592.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___187_15592.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___187_15592.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___187_15592.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___187_15592.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___187_15592.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15591 wl
              | (uu____15594,FStar_Syntax_Syntax.Tm_meta uu____15595) ->
                  let uu____15602 =
                    let uu___188_15603 = problem  in
                    let uu____15604 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___188_15603.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___188_15603.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___188_15603.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15604;
                      FStar_TypeChecker_Common.element =
                        (uu___188_15603.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___188_15603.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___188_15603.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___188_15603.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___188_15603.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___188_15603.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15602 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15606),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15608)) ->
                  let uu____15617 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15617
              | (FStar_Syntax_Syntax.Tm_bvar uu____15618,uu____15619) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15620,FStar_Syntax_Syntax.Tm_bvar uu____15621) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___142_15680 =
                    match uu___142_15680 with
                    | [] -> c
                    | bs ->
                        let uu____15702 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15702
                     in
                  let uu____15711 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15711 with
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
                                    let uu____15834 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15834
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
                  let mk_t t l uu___143_15909 =
                    match uu___143_15909 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15943 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15943 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16062 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16063 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16062
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16063 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16064,uu____16065) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16092 -> true
                    | uu____16109 -> false  in
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
                      (let uu____16150 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___189_16158 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___189_16158.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___189_16158.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___189_16158.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___189_16158.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___189_16158.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___189_16158.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___189_16158.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___189_16158.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___189_16158.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___189_16158.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___189_16158.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___189_16158.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___189_16158.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___189_16158.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___189_16158.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___189_16158.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___189_16158.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___189_16158.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___189_16158.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___189_16158.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___189_16158.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___189_16158.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___189_16158.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___189_16158.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___189_16158.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___189_16158.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___189_16158.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___189_16158.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___189_16158.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___189_16158.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___189_16158.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___189_16158.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___189_16158.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___189_16158.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___189_16158.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___189_16158.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16150 with
                       | (uu____16161,ty,uu____16163) ->
                           let uu____16164 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16164)
                     in
                  let uu____16165 =
                    let uu____16178 = maybe_eta t1  in
                    let uu____16183 = maybe_eta t2  in
                    (uu____16178, uu____16183)  in
                  (match uu____16165 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___190_16207 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___190_16207.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___190_16207.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___190_16207.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___190_16207.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___190_16207.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___190_16207.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___190_16207.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___190_16207.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16218 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16218
                       then
                         let uu____16219 = destruct_flex_t not_abs wl  in
                         (match uu____16219 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16234 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16234.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16234.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16234.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16234.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16234.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16234.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16234.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16234.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16246 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16246
                       then
                         let uu____16247 = destruct_flex_t not_abs wl  in
                         (match uu____16247 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16262 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16262.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16262.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16262.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16262.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16262.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16262.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16262.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16262.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16264 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16277,FStar_Syntax_Syntax.Tm_abs uu____16278) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16305 -> true
                    | uu____16322 -> false  in
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
                      (let uu____16363 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___189_16371 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___189_16371.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___189_16371.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___189_16371.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___189_16371.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___189_16371.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___189_16371.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___189_16371.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___189_16371.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___189_16371.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___189_16371.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___189_16371.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___189_16371.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___189_16371.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___189_16371.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___189_16371.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___189_16371.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___189_16371.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___189_16371.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___189_16371.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___189_16371.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___189_16371.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___189_16371.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___189_16371.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___189_16371.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___189_16371.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___189_16371.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___189_16371.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___189_16371.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___189_16371.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___189_16371.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___189_16371.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___189_16371.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___189_16371.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___189_16371.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___189_16371.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___189_16371.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16363 with
                       | (uu____16374,ty,uu____16376) ->
                           let uu____16377 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16377)
                     in
                  let uu____16378 =
                    let uu____16391 = maybe_eta t1  in
                    let uu____16396 = maybe_eta t2  in
                    (uu____16391, uu____16396)  in
                  (match uu____16378 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___190_16420 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___190_16420.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___190_16420.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___190_16420.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___190_16420.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___190_16420.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___190_16420.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___190_16420.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___190_16420.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16431 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16431
                       then
                         let uu____16432 = destruct_flex_t not_abs wl  in
                         (match uu____16432 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16447 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16447.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16447.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16447.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16447.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16447.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16447.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16447.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16447.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16459 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16459
                       then
                         let uu____16460 = destruct_flex_t not_abs wl  in
                         (match uu____16460 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16475 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16475.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16475.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16475.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16475.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16475.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16475.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16475.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16475.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16477 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16505 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16505) &&
                       (let uu____16509 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16509))
                      &&
                      (let uu____16516 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16516 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___144_16528 =
                             match uu___144_16528 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16529 -> true
                             | uu____16530 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16531 -> false)
                     in
                  let uu____16532 = as_refinement should_delta env wl t1  in
                  (match uu____16532 with
                   | (x11,phi1) ->
                       let uu____16539 = as_refinement should_delta env wl t2
                          in
                       (match uu____16539 with
                        | (x21,phi21) ->
                            let uu____16546 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16546 with
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
                                   let uu____16612 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16612
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16624 =
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
                                   (let uu____16638 =
                                      let uu____16639 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16639  in
                                    Prims.op_Negation uu____16638) ||
                                     (let uu____16643 =
                                        let uu____16644 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16644
                                         in
                                      Prims.op_Negation uu____16643)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16647 =
                                     let uu____16652 =
                                       let uu____16659 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16659]  in
                                     mk_t_problem wl1 uu____16652 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16647 with
                                    | (ref_prob,wl2) ->
                                        let uu____16674 =
                                          solve env1
                                            (let uu___192_16676 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___192_16676.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___192_16676.smt_ok);
                                               tcenv = (uu___192_16676.tcenv);
                                               wl_implicits =
                                                 (uu___192_16676.wl_implicits)
                                             })
                                           in
                                        (match uu____16674 with
                                         | Failed (prob,msg) ->
                                             if
                                               (Prims.op_Negation
                                                  env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                 && has_uvars
                                             then giveup env1 msg prob
                                             else fallback ()
                                         | Success uu____16686 ->
                                             let guard =
                                               let uu____16694 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16694
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___193_16703 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___193_16703.attempting);
                                                 wl_deferred =
                                                   (uu___193_16703.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___193_16703.defer_ok);
                                                 smt_ok =
                                                   (uu___193_16703.smt_ok);
                                                 tcenv =
                                                   (uu___193_16703.tcenv);
                                                 wl_implicits =
                                                   (uu___193_16703.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16705,FStar_Syntax_Syntax.Tm_uvar uu____16706) ->
                  let uu____16735 = destruct_flex_t t1 wl  in
                  (match uu____16735 with
                   | (f1,wl1) ->
                       let uu____16742 = destruct_flex_t t2 wl1  in
                       (match uu____16742 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16749;
                    FStar_Syntax_Syntax.pos = uu____16750;
                    FStar_Syntax_Syntax.vars = uu____16751;_},uu____16752),FStar_Syntax_Syntax.Tm_uvar
                 uu____16753) ->
                  let uu____16802 = destruct_flex_t t1 wl  in
                  (match uu____16802 with
                   | (f1,wl1) ->
                       let uu____16809 = destruct_flex_t t2 wl1  in
                       (match uu____16809 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16816,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16817;
                    FStar_Syntax_Syntax.pos = uu____16818;
                    FStar_Syntax_Syntax.vars = uu____16819;_},uu____16820))
                  ->
                  let uu____16869 = destruct_flex_t t1 wl  in
                  (match uu____16869 with
                   | (f1,wl1) ->
                       let uu____16876 = destruct_flex_t t2 wl1  in
                       (match uu____16876 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16883;
                    FStar_Syntax_Syntax.pos = uu____16884;
                    FStar_Syntax_Syntax.vars = uu____16885;_},uu____16886),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16887;
                    FStar_Syntax_Syntax.pos = uu____16888;
                    FStar_Syntax_Syntax.vars = uu____16889;_},uu____16890))
                  ->
                  let uu____16959 = destruct_flex_t t1 wl  in
                  (match uu____16959 with
                   | (f1,wl1) ->
                       let uu____16966 = destruct_flex_t t2 wl1  in
                       (match uu____16966 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16973,uu____16974) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16989 = destruct_flex_t t1 wl  in
                  (match uu____16989 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16996;
                    FStar_Syntax_Syntax.pos = uu____16997;
                    FStar_Syntax_Syntax.vars = uu____16998;_},uu____16999),uu____17000)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17035 = destruct_flex_t t1 wl  in
                  (match uu____17035 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17042,FStar_Syntax_Syntax.Tm_uvar uu____17043) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17058,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17059;
                    FStar_Syntax_Syntax.pos = uu____17060;
                    FStar_Syntax_Syntax.vars = uu____17061;_},uu____17062))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17097,FStar_Syntax_Syntax.Tm_arrow uu____17098) ->
                  solve_t' env
                    (let uu___194_17126 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___194_17126.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___194_17126.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___194_17126.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___194_17126.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___194_17126.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___194_17126.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___194_17126.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___194_17126.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___194_17126.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17127;
                    FStar_Syntax_Syntax.pos = uu____17128;
                    FStar_Syntax_Syntax.vars = uu____17129;_},uu____17130),FStar_Syntax_Syntax.Tm_arrow
                 uu____17131) ->
                  solve_t' env
                    (let uu___194_17179 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___194_17179.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___194_17179.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___194_17179.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___194_17179.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___194_17179.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___194_17179.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___194_17179.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___194_17179.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___194_17179.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17180,FStar_Syntax_Syntax.Tm_uvar uu____17181) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____17196,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17197;
                    FStar_Syntax_Syntax.pos = uu____17198;
                    FStar_Syntax_Syntax.vars = uu____17199;_},uu____17200))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____17235,uu____17236) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17251;
                    FStar_Syntax_Syntax.pos = uu____17252;
                    FStar_Syntax_Syntax.vars = uu____17253;_},uu____17254),uu____17255)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17290,uu____17291) ->
                  let t21 =
                    let uu____17299 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17299  in
                  solve_t env
                    (let uu___195_17325 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17325.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17325.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___195_17325.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___195_17325.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17325.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17325.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17325.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17325.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17325.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17326,FStar_Syntax_Syntax.Tm_refine uu____17327) ->
                  let t11 =
                    let uu____17335 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17335  in
                  solve_t env
                    (let uu___196_17361 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___196_17361.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___196_17361.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___196_17361.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___196_17361.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___196_17361.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___196_17361.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___196_17361.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___196_17361.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___196_17361.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17443 =
                    let uu____17444 = guard_of_prob env wl problem t1 t2  in
                    match uu____17444 with
                    | (guard,wl1) ->
                        let uu____17451 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17451
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____17662 = br1  in
                        (match uu____17662 with
                         | (p1,w1,uu____17687) ->
                             let uu____17704 = br2  in
                             (match uu____17704 with
                              | (p2,w2,uu____17723) ->
                                  let uu____17728 =
                                    let uu____17729 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____17729  in
                                  if uu____17728
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____17745 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____17745 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____17778 = br2  in
                                         (match uu____17778 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____17813 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____17813
                                                 in
                                              let uu____17824 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____17847,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____17864) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____17907 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____17907 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____17824
                                                (fun uu____17949  ->
                                                   match uu____17949 with
                                                   | (wprobs,wl2) ->
                                                       let uu____17970 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____17970
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____17985 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____17985
                                                              (fun
                                                                 uu____18009 
                                                                 ->
                                                                 match uu____18009
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18094 -> FStar_Pervasives_Native.None  in
                  let uu____18131 = solve_branches wl brs1 brs2  in
                  (match uu____18131 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18159 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18159 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18176 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18176  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18185 =
                              solve env
                                (attempt sub_probs1
                                   (let uu___197_18187 = wl3  in
                                    {
                                      attempting =
                                        (uu___197_18187.attempting);
                                      wl_deferred =
                                        (uu___197_18187.wl_deferred);
                                      ctr = (uu___197_18187.ctr);
                                      defer_ok = (uu___197_18187.defer_ok);
                                      smt_ok = false;
                                      tcenv = (uu___197_18187.tcenv);
                                      wl_implicits =
                                        (uu___197_18187.wl_implicits)
                                    }))
                               in
                            (match uu____18185 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____18191 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____18197,uu____18198) ->
                  let head1 =
                    let uu____18222 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18222
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18262 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18262
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18302 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18302
                    then
                      let uu____18303 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18304 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18305 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18303 uu____18304 uu____18305
                    else ());
                   (let uu____18307 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18307
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18314 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18314
                       then
                         let uu____18315 =
                           let uu____18322 =
                             let uu____18323 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18323 = FStar_Syntax_Util.Equal  in
                           if uu____18322
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18333 = mk_eq2 wl orig t1 t2  in
                              match uu____18333 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18315 with
                         | (guard,wl1) ->
                             let uu____18354 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18354
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18357,uu____18358) ->
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
              | (FStar_Syntax_Syntax.Tm_name uu____18501,uu____18502) ->
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
              | (FStar_Syntax_Syntax.Tm_constant uu____18639,uu____18640) ->
                  let head1 =
                    let uu____18642 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18642
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18682 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18682
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18722 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18722
                    then
                      let uu____18723 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18724 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18725 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18723 uu____18724 uu____18725
                    else ());
                   (let uu____18727 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18727
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18734 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18734
                       then
                         let uu____18735 =
                           let uu____18742 =
                             let uu____18743 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18743 = FStar_Syntax_Util.Equal  in
                           if uu____18742
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18753 = mk_eq2 wl orig t1 t2  in
                              match uu____18753 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18735 with
                         | (guard,wl1) ->
                             let uu____18774 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18774
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18777,uu____18778) ->
                  let head1 =
                    let uu____18780 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18780
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18820 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18820
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18860 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18860
                    then
                      let uu____18861 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18862 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18863 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18861 uu____18862 uu____18863
                    else ());
                   (let uu____18865 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18865
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18872 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18872
                       then
                         let uu____18873 =
                           let uu____18880 =
                             let uu____18881 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18881 = FStar_Syntax_Util.Equal  in
                           if uu____18880
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18891 = mk_eq2 wl orig t1 t2  in
                              match uu____18891 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18873 with
                         | (guard,wl1) ->
                             let uu____18912 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18912
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____18915,uu____18916) ->
                  let head1 =
                    let uu____18932 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18932
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18972 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18972
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19012 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19012
                    then
                      let uu____19013 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19014 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19015 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19013 uu____19014 uu____19015
                    else ());
                   (let uu____19017 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19017
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19024 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19024
                       then
                         let uu____19025 =
                           let uu____19032 =
                             let uu____19033 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19033 = FStar_Syntax_Util.Equal  in
                           if uu____19032
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19043 = mk_eq2 wl orig t1 t2  in
                              match uu____19043 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19025 with
                         | (guard,wl1) ->
                             let uu____19064 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19064
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19067,FStar_Syntax_Syntax.Tm_match uu____19068) ->
                  let head1 =
                    let uu____19092 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19092
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19132 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19132
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19172 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19172
                    then
                      let uu____19173 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19174 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19175 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19173 uu____19174 uu____19175
                    else ());
                   (let uu____19177 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19177
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19184 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19184
                       then
                         let uu____19185 =
                           let uu____19192 =
                             let uu____19193 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19193 = FStar_Syntax_Util.Equal  in
                           if uu____19192
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19203 = mk_eq2 wl orig t1 t2  in
                              match uu____19203 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19185 with
                         | (guard,wl1) ->
                             let uu____19224 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19224
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19227,FStar_Syntax_Syntax.Tm_uinst uu____19228) ->
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
              | (uu____19371,FStar_Syntax_Syntax.Tm_name uu____19372) ->
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
              | (uu____19509,FStar_Syntax_Syntax.Tm_constant uu____19510) ->
                  let head1 =
                    let uu____19512 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19512
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19552 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19552
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19592 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19592
                    then
                      let uu____19593 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19594 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19595 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19593 uu____19594 uu____19595
                    else ());
                   (let uu____19597 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19597
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19604 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19604
                       then
                         let uu____19605 =
                           let uu____19612 =
                             let uu____19613 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19613 = FStar_Syntax_Util.Equal  in
                           if uu____19612
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19623 = mk_eq2 wl orig t1 t2  in
                              match uu____19623 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19605 with
                         | (guard,wl1) ->
                             let uu____19644 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19644
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19647,FStar_Syntax_Syntax.Tm_fvar uu____19648) ->
                  let head1 =
                    let uu____19650 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19650
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19690 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19690
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19730 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19730
                    then
                      let uu____19731 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19732 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19733 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19731 uu____19732 uu____19733
                    else ());
                   (let uu____19735 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19735
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19742 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19742
                       then
                         let uu____19743 =
                           let uu____19750 =
                             let uu____19751 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19751 = FStar_Syntax_Util.Equal  in
                           if uu____19750
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19761 = mk_eq2 wl orig t1 t2  in
                              match uu____19761 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19743 with
                         | (guard,wl1) ->
                             let uu____19782 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19782
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19785,FStar_Syntax_Syntax.Tm_app uu____19786) ->
                  let head1 =
                    let uu____19802 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19802
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19842 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19842
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19882 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19882
                    then
                      let uu____19883 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19884 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19885 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19883 uu____19884 uu____19885
                    else ());
                   (let uu____19887 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19887
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19894 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19894
                       then
                         let uu____19895 =
                           let uu____19902 =
                             let uu____19903 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19903 = FStar_Syntax_Util.Equal  in
                           if uu____19902
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19913 = mk_eq2 wl orig t1 t2  in
                              match uu____19913 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19895 with
                         | (guard,wl1) ->
                             let uu____19934 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19934
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____19937,FStar_Syntax_Syntax.Tm_let uu____19938) ->
                  let uu____19963 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____19963
                  then
                    let uu____19964 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____19964
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____19966,uu____19967) ->
                  let uu____19980 =
                    let uu____19985 =
                      let uu____19986 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19987 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19988 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19989 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19986 uu____19987 uu____19988 uu____19989
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19985)
                     in
                  FStar_Errors.raise_error uu____19980
                    t1.FStar_Syntax_Syntax.pos
              | (uu____19990,FStar_Syntax_Syntax.Tm_let uu____19991) ->
                  let uu____20004 =
                    let uu____20009 =
                      let uu____20010 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20011 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20012 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20013 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20010 uu____20011 uu____20012 uu____20013
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20009)
                     in
                  FStar_Errors.raise_error uu____20004
                    t1.FStar_Syntax_Syntax.pos
              | uu____20014 -> giveup env "head tag mismatch" orig))))

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
          (let uu____20073 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20073
           then
             let uu____20074 =
               let uu____20075 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____20075  in
             let uu____20076 =
               let uu____20077 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____20077  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____20074 uu____20076
           else ());
          (let uu____20079 =
             let uu____20080 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____20080  in
           if uu____20079
           then
             let uu____20081 =
               let uu____20082 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20083 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20082 uu____20083
                in
             giveup env uu____20081 orig
           else
             (let uu____20085 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____20085 with
              | (ret_sub_prob,wl1) ->
                  let uu____20092 =
                    FStar_List.fold_right2
                      (fun uu____20125  ->
                         fun uu____20126  ->
                           fun uu____20127  ->
                             match (uu____20125, uu____20126, uu____20127)
                             with
                             | ((a1,uu____20163),(a2,uu____20165),(arg_sub_probs,wl2))
                                 ->
                                 let uu____20186 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____20186 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____20092 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____20215 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____20215  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20245 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20248)::[] -> wp1
              | uu____20265 ->
                  let uu____20274 =
                    let uu____20275 =
                      let uu____20276 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20276  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20275
                     in
                  failwith uu____20274
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20282 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20282]
              | x -> x  in
            let uu____20284 =
              let uu____20293 =
                let uu____20300 =
                  let uu____20301 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20301 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20300  in
              [uu____20293]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20284;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20314 = lift_c1 ()  in solve_eq uu____20314 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___145_20320  ->
                       match uu___145_20320 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20321 -> false))
                in
             let uu____20322 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20348)::uu____20349,(wp2,uu____20351)::uu____20352)
                   -> (wp1, wp2)
               | uu____20405 ->
                   let uu____20426 =
                     let uu____20431 =
                       let uu____20432 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20433 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20432 uu____20433
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20431)
                      in
                   FStar_Errors.raise_error uu____20426
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20322 with
             | (wpc1,wpc2) ->
                 let uu____20440 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20440
                 then
                   let uu____20443 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20443 wl
                 else
                   (let uu____20445 =
                      let uu____20452 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20452  in
                    match uu____20445 with
                    | (c2_decl,qualifiers) ->
                        let uu____20473 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20473
                        then
                          let c1_repr =
                            let uu____20477 =
                              let uu____20478 =
                                let uu____20479 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20479  in
                              let uu____20480 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20478 uu____20480
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20477
                             in
                          let c2_repr =
                            let uu____20482 =
                              let uu____20483 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20484 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20483 uu____20484
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20482
                             in
                          let uu____20485 =
                            let uu____20490 =
                              let uu____20491 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20492 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20491 uu____20492
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20490
                             in
                          (match uu____20485 with
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
                                 ((let uu____20506 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20506
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20509 =
                                     let uu____20516 =
                                       let uu____20517 =
                                         let uu____20532 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20535 =
                                           let uu____20544 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20551 =
                                             let uu____20560 =
                                               let uu____20567 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20567
                                                in
                                             [uu____20560]  in
                                           uu____20544 :: uu____20551  in
                                         (uu____20532, uu____20535)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20517
                                        in
                                     FStar_Syntax_Syntax.mk uu____20516  in
                                   uu____20509 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20602 =
                                    let uu____20609 =
                                      let uu____20610 =
                                        let uu____20625 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20628 =
                                          let uu____20637 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20644 =
                                            let uu____20653 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20660 =
                                              let uu____20669 =
                                                let uu____20676 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20676
                                                 in
                                              [uu____20669]  in
                                            uu____20653 :: uu____20660  in
                                          uu____20637 :: uu____20644  in
                                        (uu____20625, uu____20628)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20610
                                       in
                                    FStar_Syntax_Syntax.mk uu____20609  in
                                  uu____20602 FStar_Pervasives_Native.None r)
                              in
                           let uu____20714 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20714 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20722 =
                                   let uu____20725 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____20725
                                    in
                                 solve_prob orig uu____20722 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____20732 = FStar_Util.physical_equality c1 c2  in
        if uu____20732
        then
          let uu____20733 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20733
        else
          ((let uu____20736 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20736
            then
              let uu____20737 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20738 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20737
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20738
            else ());
           (let uu____20740 =
              let uu____20749 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20752 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20749, uu____20752)  in
            match uu____20740 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20770),FStar_Syntax_Syntax.Total
                    (t2,uu____20772)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20789 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20789 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20790,FStar_Syntax_Syntax.Total uu____20791) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20809),FStar_Syntax_Syntax.Total
                    (t2,uu____20811)) ->
                     let uu____20828 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20828 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20830),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20832)) ->
                     let uu____20849 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20849 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20851),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20853)) ->
                     let uu____20870 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20870 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20871,FStar_Syntax_Syntax.Comp uu____20872) ->
                     let uu____20881 =
                       let uu___198_20884 = problem  in
                       let uu____20887 =
                         let uu____20888 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20888
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___198_20884.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20887;
                         FStar_TypeChecker_Common.relation =
                           (uu___198_20884.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___198_20884.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___198_20884.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___198_20884.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___198_20884.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___198_20884.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___198_20884.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___198_20884.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20881 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20889,FStar_Syntax_Syntax.Comp uu____20890) ->
                     let uu____20899 =
                       let uu___198_20902 = problem  in
                       let uu____20905 =
                         let uu____20906 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20906
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___198_20902.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20905;
                         FStar_TypeChecker_Common.relation =
                           (uu___198_20902.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___198_20902.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___198_20902.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___198_20902.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___198_20902.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___198_20902.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___198_20902.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___198_20902.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20899 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20907,FStar_Syntax_Syntax.GTotal uu____20908) ->
                     let uu____20917 =
                       let uu___199_20920 = problem  in
                       let uu____20923 =
                         let uu____20924 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20924
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_20920.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___199_20920.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___199_20920.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20923;
                         FStar_TypeChecker_Common.element =
                           (uu___199_20920.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_20920.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_20920.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_20920.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_20920.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_20920.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20917 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20925,FStar_Syntax_Syntax.Total uu____20926) ->
                     let uu____20935 =
                       let uu___199_20938 = problem  in
                       let uu____20941 =
                         let uu____20942 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20942
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_20938.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___199_20938.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___199_20938.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20941;
                         FStar_TypeChecker_Common.element =
                           (uu___199_20938.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_20938.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_20938.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_20938.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_20938.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_20938.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20935 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20943,FStar_Syntax_Syntax.Comp uu____20944) ->
                     let uu____20945 =
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
                     if uu____20945
                     then
                       let uu____20946 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____20946 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20950 =
                            let uu____20955 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____20955
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20961 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____20962 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____20961, uu____20962))
                             in
                          match uu____20950 with
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
                           (let uu____20969 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____20969
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20971 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____20971 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20974 =
                                  let uu____20975 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____20976 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____20975 uu____20976
                                   in
                                giveup env uu____20974 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____20983 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21011  ->
              match uu____21011 with
              | (uu____21020,tm,uu____21022,uu____21023) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____20983 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21056 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21056 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21074 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21102  ->
                match uu____21102 with
                | (u1,u2) ->
                    let uu____21109 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21110 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21109 uu____21110))
         in
      FStar_All.pipe_right uu____21074 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21137,[])) -> "{}"
      | uu____21162 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21185 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21185
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21188 =
              FStar_List.map
                (fun uu____21198  ->
                   match uu____21198 with
                   | (uu____21203,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21188 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21208 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21208 imps
  
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
                  let uu____21261 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21261
                  then
                    let uu____21262 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21263 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21262
                      (rel_to_string rel) uu____21263
                  else "TOP"  in
                let uu____21265 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21265 with
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
              let uu____21322 =
                let uu____21325 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21325
                 in
              FStar_Syntax_Syntax.new_bv uu____21322 t1  in
            let uu____21328 =
              let uu____21333 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21333
               in
            match uu____21328 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____21389 = FStar_Options.eager_inference ()  in
          if uu____21389
          then
            let uu___200_21390 = probs  in
            {
              attempting = (uu___200_21390.attempting);
              wl_deferred = (uu___200_21390.wl_deferred);
              ctr = (uu___200_21390.ctr);
              defer_ok = false;
              smt_ok = (uu___200_21390.smt_ok);
              tcenv = (uu___200_21390.tcenv);
              wl_implicits = (uu___200_21390.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21410 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21410
              then
                let uu____21411 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21411
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
          ((let uu____21433 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21433
            then
              let uu____21434 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21434
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21438 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21438
             then
               let uu____21439 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21439
             else ());
            (let f2 =
               let uu____21442 =
                 let uu____21443 = FStar_Syntax_Util.unmeta f1  in
                 uu____21443.FStar_Syntax_Syntax.n  in
               match uu____21442 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21447 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___201_21448 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___201_21448.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___201_21448.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___201_21448.FStar_TypeChecker_Env.implicits)
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
            let uu____21550 =
              let uu____21551 =
                let uu____21552 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21552;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21551  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21550
  
let with_guard_no_simp :
  'Auu____21567 .
    'Auu____21567 ->
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
            let uu____21590 =
              let uu____21591 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21591;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21590
  
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
          (let uu____21629 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21629
           then
             let uu____21630 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21631 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21630
               uu____21631
           else ());
          (let uu____21633 =
             let uu____21638 = empty_worklist env  in
             let uu____21639 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____21638 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____21639
              in
           match uu____21633 with
           | (prob,wl) ->
               let g =
                 let uu____21647 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21665  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21647  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21707 = try_teq true env t1 t2  in
        match uu____21707 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21711 = FStar_TypeChecker_Env.get_range env  in
              let uu____21712 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21711 uu____21712);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21719 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21719
              then
                let uu____21720 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21721 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21722 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21720
                  uu____21721 uu____21722
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
          let uu____21744 = FStar_TypeChecker_Env.get_range env  in
          let uu____21745 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21744 uu____21745
  
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
        (let uu____21770 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21770
         then
           let uu____21771 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21772 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21771 uu____21772
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21775 =
           let uu____21782 = empty_worklist env  in
           let uu____21783 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____21782 env c1 rel c2 FStar_Pervasives_Native.None
             uu____21783 "sub_comp"
            in
         match uu____21775 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21793 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21811  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21793)
  
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
      fun uu____21864  ->
        match uu____21864 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21907 =
                 let uu____21912 =
                   let uu____21913 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21914 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21913 uu____21914
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21912)  in
               let uu____21915 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21907 uu____21915)
               in
            let equiv1 v1 v' =
              let uu____21927 =
                let uu____21932 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21933 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21932, uu____21933)  in
              match uu____21927 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21952 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21982 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____21982 with
                      | FStar_Syntax_Syntax.U_unif uu____21989 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22018  ->
                                    match uu____22018 with
                                    | (u,v') ->
                                        let uu____22027 = equiv1 v1 v'  in
                                        if uu____22027
                                        then
                                          let uu____22030 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22030 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22046 -> []))
               in
            let uu____22051 =
              let wl =
                let uu___202_22055 = empty_worklist env  in
                {
                  attempting = (uu___202_22055.attempting);
                  wl_deferred = (uu___202_22055.wl_deferred);
                  ctr = (uu___202_22055.ctr);
                  defer_ok = false;
                  smt_ok = (uu___202_22055.smt_ok);
                  tcenv = (uu___202_22055.tcenv);
                  wl_implicits = (uu___202_22055.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22073  ->
                      match uu____22073 with
                      | (lb,v1) ->
                          let uu____22080 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22080 with
                           | USolved wl1 -> ()
                           | uu____22082 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22092 =
              match uu____22092 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22101) -> true
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
                      uu____22124,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22126,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22137) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22144,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22152 -> false)
               in
            let uu____22157 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22172  ->
                      match uu____22172 with
                      | (u,v1) ->
                          let uu____22179 = check_ineq (u, v1)  in
                          if uu____22179
                          then true
                          else
                            ((let uu____22182 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22182
                              then
                                let uu____22183 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22184 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22183
                                  uu____22184
                              else ());
                             false)))
               in
            if uu____22157
            then ()
            else
              ((let uu____22188 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22188
                then
                  ((let uu____22190 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22190);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22200 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22200))
                else ());
               (let uu____22210 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22210))
  
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
        let fail1 uu____22277 =
          match uu____22277 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___203_22298 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___203_22298.attempting);
            wl_deferred = (uu___203_22298.wl_deferred);
            ctr = (uu___203_22298.ctr);
            defer_ok;
            smt_ok = (uu___203_22298.smt_ok);
            tcenv = (uu___203_22298.tcenv);
            wl_implicits = (uu___203_22298.wl_implicits)
          }  in
        (let uu____22300 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22300
         then
           let uu____22301 = FStar_Util.string_of_bool defer_ok  in
           let uu____22302 = wl_to_string wl  in
           let uu____22303 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22301 uu____22302 uu____22303
         else ());
        (let g1 =
           let uu____22314 = solve_and_commit env wl fail1  in
           match uu____22314 with
           | FStar_Pervasives_Native.Some
               (uu____22321::uu____22322,uu____22323) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___204_22348 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___204_22348.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___204_22348.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22357 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___205_22365 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___205_22365.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___205_22365.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___205_22365.FStar_TypeChecker_Env.implicits)
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
    let uu____22413 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22413 with
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
            let uu___206_22536 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___206_22536.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___206_22536.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___206_22536.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22537 =
            let uu____22538 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22538  in
          if uu____22537
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22546 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22547 =
                       let uu____22548 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22548
                        in
                     FStar_Errors.diag uu____22546 uu____22547)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22552 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22553 =
                        let uu____22554 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22554
                         in
                      FStar_Errors.diag uu____22552 uu____22553)
                   else ();
                   (let uu____22557 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22557 "discharge_guard'"
                      env vc1);
                   (let uu____22558 = check_trivial vc1  in
                    match uu____22558 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22565 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22566 =
                                let uu____22567 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22567
                                 in
                              FStar_Errors.diag uu____22565 uu____22566)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22572 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22573 =
                                let uu____22574 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22574
                                 in
                              FStar_Errors.diag uu____22572 uu____22573)
                           else ();
                           (let vcs =
                              let uu____22587 = FStar_Options.use_tactics ()
                                 in
                              if uu____22587
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22609  ->
                                     (let uu____22611 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22611);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22654  ->
                                              match uu____22654 with
                                              | (env1,goal,opts) ->
                                                  let uu____22670 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22670, opts)))))
                              else
                                (let uu____22672 =
                                   let uu____22679 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22679)  in
                                 [uu____22672])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22716  ->
                                    match uu____22716 with
                                    | (env1,goal,opts) ->
                                        let uu____22732 = check_trivial goal
                                           in
                                        (match uu____22732 with
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
                                                (let uu____22740 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22741 =
                                                   let uu____22742 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22743 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22742 uu____22743
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22740 uu____22741)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22746 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22747 =
                                                   let uu____22748 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22748
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22746 uu____22747)
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
      let uu____22762 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22762 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22769 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22769
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22780 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22780 with
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
            let uu____22813 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____22813 with
            | FStar_Pervasives_Native.Some uu____22816 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____22836 = acc  in
            match uu____22836 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22888 = hd1  in
                     (match uu____22888 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____22902 = unresolved ctx_u  in
                             if uu____22902
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___207_22914 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___207_22914.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___207_22914.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___207_22914.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___207_22914.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___207_22914.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___207_22914.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___207_22914.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___207_22914.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___207_22914.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___207_22914.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___207_22914.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___207_22914.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___207_22914.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___207_22914.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___207_22914.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___207_22914.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___207_22914.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___207_22914.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___207_22914.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___207_22914.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___207_22914.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___207_22914.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___207_22914.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___207_22914.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___207_22914.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___207_22914.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___207_22914.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___207_22914.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___207_22914.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___207_22914.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___207_22914.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___207_22914.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___207_22914.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___207_22914.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___207_22914.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___207_22914.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___207_22914.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___207_22914.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___208_22917 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___208_22917.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___208_22917.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___208_22917.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___208_22917.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___208_22917.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___208_22917.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___208_22917.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___208_22917.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___208_22917.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___208_22917.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___208_22917.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___208_22917.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___208_22917.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___208_22917.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___208_22917.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___208_22917.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___208_22917.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___208_22917.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___208_22917.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___208_22917.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___208_22917.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___208_22917.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___208_22917.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___208_22917.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___208_22917.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___208_22917.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___208_22917.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___208_22917.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___208_22917.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___208_22917.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___208_22917.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___208_22917.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___208_22917.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___208_22917.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___208_22917.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___208_22917.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___208_22917.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___208_22917.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____22920 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22920
                                   then
                                     let uu____22921 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____22922 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____22923 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____22924 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____22921 uu____22922 uu____22923
                                       reason uu____22924
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____22935 =
                                             let uu____22944 =
                                               let uu____22951 =
                                                 let uu____22952 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____22953 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____22954 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____22952 uu____22953
                                                   uu____22954
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____22951, r)
                                                in
                                             [uu____22944]  in
                                           FStar_Errors.add_errors
                                             uu____22935);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___211_22968 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___211_22968.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___211_22968.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___211_22968.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____22971 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____22981  ->
                                               let uu____22982 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____22983 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____22984 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____22982 uu____22983
                                                 reason uu____22984)) env2 g2
                                         true
                                        in
                                     match uu____22971 with
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
          let uu___212_22994 = g  in
          let uu____22995 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___212_22994.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___212_22994.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___212_22994.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____22995
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
        let uu____23045 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23045 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23054 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23054
      | (reason,e,ctx_u,r)::uu____23059 ->
          let uu____23078 =
            let uu____23083 =
              let uu____23084 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23085 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23084 uu____23085 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23083)
             in
          FStar_Errors.raise_error uu____23078 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___213_23096 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___213_23096.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___213_23096.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___213_23096.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23111 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23111 with
      | FStar_Pervasives_Native.Some uu____23117 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23133 = try_teq false env t1 t2  in
        match uu____23133 with
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
        (let uu____23167 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23167
         then
           let uu____23168 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23169 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23168
             uu____23169
         else ());
        (let uu____23171 =
           let uu____23178 = empty_worklist env  in
           new_t_prob uu____23178 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23171 with
         | (prob,x,wl) ->
             let g =
               let uu____23191 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23209  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23191  in
             ((let uu____23237 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23237
               then
                 let uu____23238 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23239 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23240 =
                   let uu____23241 = FStar_Util.must g  in
                   guard_to_string env uu____23241  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23238 uu____23239 uu____23240
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
        let uu____23275 = check_subtyping env t1 t2  in
        match uu____23275 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23294 =
              let uu____23295 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23295 g  in
            FStar_Pervasives_Native.Some uu____23294
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23313 = check_subtyping env t1 t2  in
        match uu____23313 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23332 =
              let uu____23333 =
                let uu____23334 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23334]  in
              close_guard env uu____23333 g  in
            FStar_Pervasives_Native.Some uu____23332
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23363 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23363
         then
           let uu____23364 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23365 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23364
             uu____23365
         else ());
        (let uu____23367 =
           let uu____23374 = empty_worklist env  in
           new_t_prob uu____23374 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23367 with
         | (prob,x,wl) ->
             let g =
               let uu____23381 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23399  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23381  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23428 =
                      let uu____23429 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23429]  in
                    close_guard env uu____23428 g1  in
                  discharge_guard_nosmt env g2))
  