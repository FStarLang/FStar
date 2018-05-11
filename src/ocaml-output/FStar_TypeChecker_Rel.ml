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
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = true;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___152_1408 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___152_1408.wl_deferred);
          ctr = (uu___152_1408.ctr);
          defer_ok = (uu___152_1408.defer_ok);
          smt_ok;
          tcenv = (uu___152_1408.tcenv);
          wl_implicits = (uu___152_1408.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1415 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1415,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___153_1438 = empty_worklist env  in
      let uu____1439 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1439;
        wl_deferred = (uu___153_1438.wl_deferred);
        ctr = (uu___153_1438.ctr);
        defer_ok = (uu___153_1438.defer_ok);
        smt_ok = (uu___153_1438.smt_ok);
        tcenv = (uu___153_1438.tcenv);
        wl_implicits = (uu___153_1438.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___154_1459 = wl  in
        {
          attempting = (uu___154_1459.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___154_1459.ctr);
          defer_ok = (uu___154_1459.defer_ok);
          smt_ok = (uu___154_1459.smt_ok);
          tcenv = (uu___154_1459.tcenv);
          wl_implicits = (uu___154_1459.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___155_1480 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___155_1480.wl_deferred);
        ctr = (uu___155_1480.ctr);
        defer_ok = (uu___155_1480.defer_ok);
        smt_ok = (uu___155_1480.smt_ok);
        tcenv = (uu___155_1480.tcenv);
        wl_implicits = (uu___155_1480.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1497 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1497
         then
           let uu____1498 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1498
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___117_1504  ->
    match uu___117_1504 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1509 .
    'Auu____1509 FStar_TypeChecker_Common.problem ->
      'Auu____1509 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___156_1521 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___156_1521.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___156_1521.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___156_1521.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___156_1521.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___156_1521.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___156_1521.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___156_1521.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1528 .
    'Auu____1528 FStar_TypeChecker_Common.problem ->
      'Auu____1528 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___118_1545  ->
    match uu___118_1545 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.TProb _0_17)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.CProb _0_18)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___119_1560  ->
    match uu___119_1560 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___157_1566 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___157_1566.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___157_1566.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___157_1566.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___157_1566.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___157_1566.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___157_1566.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___157_1566.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___157_1566.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___157_1566.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___158_1574 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___158_1574.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___158_1574.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___158_1574.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___158_1574.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___158_1574.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___158_1574.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___158_1574.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___158_1574.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___158_1574.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___120_1586  ->
      match uu___120_1586 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___121_1591  ->
    match uu___121_1591 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___122_1602  ->
    match uu___122_1602 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___123_1615  ->
    match uu___123_1615 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___124_1628  ->
    match uu___124_1628 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___125_1639  ->
    match uu___125_1639 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___126_1654  ->
    match uu___126_1654 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1673 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1673) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1701 =
          let uu____1702 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1702  in
        if uu____1701
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1736)::bs ->
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
        let uu____1803 =
          let uu____1804 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1804  in
        if uu____1803
        then ()
        else
          (let uu____1806 =
             let uu____1809 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1809
              in
           def_check_closed_in (p_loc prob) msg uu____1806 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1839 =
         let uu____1840 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1840  in
       if uu____1839
       then ()
       else
         (let uu____1842 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1842));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1854 -> ())
  
let mk_eq2 :
  'Auu____1866 .
    worklist ->
      'Auu____1866 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1895 = FStar_Syntax_Util.type_u ()  in
          match uu____1895 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1907 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1907 with
               | (uu____1918,tt,wl1) ->
                   let uu____1921 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1921, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___127_1926  ->
    match uu___127_1926 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1942 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1942 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1952  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2050 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2050 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2050 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2050 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2116 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2116  in
                  let uu____2119 =
                    let uu____2126 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2126
                      guard_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2119 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2147 ->
                            let uu____2154 =
                              let uu____2159 =
                                FStar_List.map
                                  (fun uu____2172  ->
                                     match uu____2172 with
                                     | (x,i) ->
                                         let uu____2183 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2183, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2159  in
                            uu____2154 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2186 =
                        let uu____2189 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2189;
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
                      (uu____2186, wl1)
  
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
                  let uu____2252 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2252 with
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
                  let uu____2329 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2329 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2364 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2364 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2364 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2364 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2415 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2452 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2452]  in
                        let uu____2465 =
                          let uu____2468 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2468  in
                        let uu____2471 =
                          let uu____2474 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2474  in
                        (bs, uu____2465, uu____2471)
                     in
                  match uu____2415 with
                  | (bs,lg_ty,elt) ->
                      let uu____2496 =
                        let uu____2503 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___159_2511 = wl  in
                           {
                             attempting = (uu___159_2511.attempting);
                             wl_deferred = (uu___159_2511.wl_deferred);
                             ctr = (uu___159_2511.ctr);
                             defer_ok = (uu___159_2511.defer_ok);
                             smt_ok = (uu___159_2511.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___159_2511.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2503
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2496 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2523 =
                                   let uu____2528 =
                                     let uu____2529 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2529]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2528
                                    in
                                 uu____2523 FStar_Pervasives_Native.None loc
                              in
                           let uu____2550 =
                             let uu____2553 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2553;
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
                           (uu____2550, wl1))
  
let problem_using_guard :
  'Auu____2570 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2570 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2570 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2570 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2607 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2607;
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
  'Auu____2618 .
    worklist ->
      'Auu____2618 FStar_TypeChecker_Common.problem ->
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
        let uu____2668 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2668
        then
          let uu____2669 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2670 = prob_to_string env d  in
          let uu____2671 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2669 uu____2670 uu____2671 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2677 -> failwith "impossible"  in
           let uu____2678 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2690 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2691 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2690, uu____2691)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2695 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2696 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2695, uu____2696)
              in
           match uu____2678 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___128_2714  ->
            match uu___128_2714 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2726 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___129_2748  ->
           match uu___129_2748 with
           | UNIV uu____2751 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2758 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2758
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
        (fun uu___130_2782  ->
           match uu___130_2782 with
           | UNIV (u',t) ->
               let uu____2787 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2787
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2791 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2802 =
        let uu____2803 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2803
         in
      FStar_Syntax_Subst.compress uu____2802
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2814 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2814
  
let norm_arg :
  'Auu____2821 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2821) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2821)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2844 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2844, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2885  ->
              match uu____2885 with
              | (x,imp) ->
                  let uu____2896 =
                    let uu___160_2897 = x  in
                    let uu____2898 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___160_2897.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___160_2897.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2898
                    }  in
                  (uu____2896, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2919 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2919
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2923 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2923
        | uu____2926 -> u2  in
      let uu____2927 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2927
  
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
                (let uu____3049 = norm_refinement env t12  in
                 match uu____3049 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3066;
                     FStar_Syntax_Syntax.vars = uu____3067;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3093 =
                       let uu____3094 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3095 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3094 uu____3095
                        in
                     failwith uu____3093)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3111 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3111
          | FStar_Syntax_Syntax.Tm_uinst uu____3112 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3151 =
                   let uu____3152 = FStar_Syntax_Subst.compress t1'  in
                   uu____3152.FStar_Syntax_Syntax.n  in
                 match uu____3151 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3169 -> aux true t1'
                 | uu____3176 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3193 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3226 =
                   let uu____3227 = FStar_Syntax_Subst.compress t1'  in
                   uu____3227.FStar_Syntax_Syntax.n  in
                 match uu____3226 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3244 -> aux true t1'
                 | uu____3251 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3268 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3315 =
                   let uu____3316 = FStar_Syntax_Subst.compress t1'  in
                   uu____3316.FStar_Syntax_Syntax.n  in
                 match uu____3315 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3333 -> aux true t1'
                 | uu____3340 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3357 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3374 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3391 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3408 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3425 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3454 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3487 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3510 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3541 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3570 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3609 ->
              let uu____3616 =
                let uu____3617 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3618 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3617 uu____3618
                 in
              failwith uu____3616
          | FStar_Syntax_Syntax.Tm_ascribed uu____3633 ->
              let uu____3660 =
                let uu____3661 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3662 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3661 uu____3662
                 in
              failwith uu____3660
          | FStar_Syntax_Syntax.Tm_delayed uu____3677 ->
              let uu____3702 =
                let uu____3703 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3704 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3703 uu____3704
                 in
              failwith uu____3702
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3719 =
                let uu____3720 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3721 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3720 uu____3721
                 in
              failwith uu____3719
           in
        let uu____3736 = whnf env t1  in aux false uu____3736
  
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
      let uu____3782 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3782 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3818 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3818, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3829 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3829 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3856 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3856 with
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
  fun uu____3943  ->
    match uu____3943 with
    | (t_base,refopt) ->
        let uu____3976 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3976 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4016 =
      let uu____4019 =
        let uu____4022 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4045  ->
                  match uu____4045 with | (uu____4052,uu____4053,x) -> x))
           in
        FStar_List.append wl.attempting uu____4022  in
      FStar_List.map (wl_prob_to_string wl) uu____4019  in
    FStar_All.pipe_right uu____4016 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4067 .
    ('Auu____4067,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4078  ->
    match uu____4078 with
    | (uu____4085,c,args) ->
        let uu____4088 = print_ctx_uvar c  in
        let uu____4089 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4088 uu____4089
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4095 = FStar_Syntax_Util.head_and_args t  in
    match uu____4095 with
    | (head1,_args) ->
        let uu____4132 =
          let uu____4133 = FStar_Syntax_Subst.compress head1  in
          uu____4133.FStar_Syntax_Syntax.n  in
        (match uu____4132 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4136 -> true
         | uu____4151 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4157 = FStar_Syntax_Util.head_and_args t  in
    match uu____4157 with
    | (head1,_args) ->
        let uu____4194 =
          let uu____4195 = FStar_Syntax_Subst.compress head1  in
          uu____4195.FStar_Syntax_Syntax.n  in
        (match uu____4194 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4199) -> u
         | uu____4220 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4243 = FStar_Syntax_Util.head_and_args t  in
      match uu____4243 with
      | (head1,args) ->
          let uu____4284 =
            let uu____4285 = FStar_Syntax_Subst.compress head1  in
            uu____4285.FStar_Syntax_Syntax.n  in
          (match uu____4284 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4293)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4336 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___131_4361  ->
                         match uu___131_4361 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4365 =
                               let uu____4366 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4366.FStar_Syntax_Syntax.n  in
                             (match uu____4365 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4370 -> false)
                         | uu____4371 -> true))
                  in
               (match uu____4336 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4393 =
                        FStar_List.collect
                          (fun uu___132_4403  ->
                             match uu___132_4403 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4407 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4407]
                             | uu____4408 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4393 FStar_List.rev  in
                    let uu____4425 =
                      let uu____4432 =
                        let uu____4439 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___133_4457  ->
                                  match uu___133_4457 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4461 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4461]
                                  | uu____4462 -> []))
                           in
                        FStar_All.pipe_right uu____4439 FStar_List.rev  in
                      let uu____4479 =
                        let uu____4482 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4482  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4432 uu____4479
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4425 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4511  ->
                                match uu____4511 with
                                | (x,i) ->
                                    let uu____4522 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4522, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4545  ->
                                match uu____4545 with
                                | (a,i) ->
                                    let uu____4556 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4556, i)) args_sol
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
           | uu____4572 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4592 =
          let uu____4613 =
            let uu____4614 = FStar_Syntax_Subst.compress k  in
            uu____4614.FStar_Syntax_Syntax.n  in
          match uu____4613 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4683 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4683)
              else
                (let uu____4713 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4713 with
                 | (ys',t1,uu____4744) ->
                     let uu____4749 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4749))
          | uu____4782 ->
              let uu____4783 =
                let uu____4788 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4788)  in
              ((ys, t), uu____4783)
           in
        match uu____4592 with
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
                 let uu____4865 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4865 c  in
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
               (let uu____4939 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4939
                then
                  let uu____4940 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4941 = print_ctx_uvar uv  in
                  let uu____4942 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4940 uu____4941 uu____4942
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
             let uu____4948 = p_guard_uvar prob  in
             match uu____4948 with
             | (xs,uv) ->
                 let fail1 uu____4960 =
                   let uu____4961 =
                     let uu____4962 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4963 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4962 uu____4963
                      in
                   failwith uu____4961  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____5013  ->
                           match uu____5013 with
                           | (a,i) ->
                               let uu____5026 =
                                 let uu____5027 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____5027.FStar_Syntax_Syntax.n  in
                               (match uu____5026 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____5045 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____5053 =
                     let uu____5054 = is_flex g  in
                     Prims.op_Negation uu____5054  in
                   if uu____5053
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____5058 = destruct_flex_t g wl  in
                      match uu____5058 with
                      | ((uu____5063,uv1,args),wl1) ->
                          ((let uu____5068 = args_as_binders args  in
                            assign_solution uu____5068 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___161_5070 = wl1  in
                   {
                     attempting = (uu___161_5070.attempting);
                     wl_deferred = (uu___161_5070.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___161_5070.defer_ok);
                     smt_ok = (uu___161_5070.smt_ok);
                     tcenv = (uu___161_5070.tcenv);
                     wl_implicits = (uu___161_5070.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5091 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5091
         then
           let uu____5092 = FStar_Util.string_of_int pid  in
           let uu____5093 =
             let uu____5094 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5094 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5092 uu____5093
         else ());
        commit sol;
        (let uu___162_5101 = wl  in
         {
           attempting = (uu___162_5101.attempting);
           wl_deferred = (uu___162_5101.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___162_5101.defer_ok);
           smt_ok = (uu___162_5101.smt_ok);
           tcenv = (uu___162_5101.tcenv);
           wl_implicits = (uu___162_5101.wl_implicits)
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
             | (uu____5163,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5191 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5191
              in
           (let uu____5197 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5197
            then
              let uu____5198 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5199 =
                let uu____5200 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5200 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5198 uu____5199
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
        let uu____5225 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5225 FStar_Util.set_elements  in
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
      let uu____5259 = occurs uk t  in
      match uu____5259 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5288 =
                 let uu____5289 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5290 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5289 uu____5290
                  in
               FStar_Pervasives_Native.Some uu____5288)
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
            let uu____5379 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5379 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5423 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5471  ->
             match uu____5471 with
             | (x,uu____5481) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5494 = FStar_List.last bs  in
      match uu____5494 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5512) ->
          let uu____5517 =
            FStar_Util.prefix_until
              (fun uu___134_5532  ->
                 match uu___134_5532 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5534 -> false) g
             in
          (match uu____5517 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5547,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5583 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5583 with
        | (pfx,uu____5593) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5605 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5605 with
             | (uu____5612,src',wl1) ->
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
                 | uu____5712 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5713 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5767  ->
                  fun uu____5768  ->
                    match (uu____5767, uu____5768) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5849 =
                          let uu____5850 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5850
                           in
                        if uu____5849
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5875 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5875
                           then
                             let uu____5888 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5888)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5713 with | (isect,uu____5925) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5954 'Auu____5955 .
    (FStar_Syntax_Syntax.bv,'Auu____5954) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5955) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6012  ->
              fun uu____6013  ->
                match (uu____6012, uu____6013) with
                | ((a,uu____6031),(b,uu____6033)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6048 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6048) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6078  ->
           match uu____6078 with
           | (y,uu____6084) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6093 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6093) FStar_Pervasives_Native.tuple2
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
                   let uu____6223 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6223
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6243 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6286 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6324 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6337 -> false
  
let string_of_option :
  'Auu____6344 .
    ('Auu____6344 -> Prims.string) ->
      'Auu____6344 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___135_6359  ->
      match uu___135_6359 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6365 = f x  in Prims.strcat "Some " uu____6365
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___136_6370  ->
    match uu___136_6370 with
    | MisMatch (d1,d2) ->
        let uu____6381 =
          let uu____6382 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6383 =
            let uu____6384 =
              let uu____6385 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6385 ")"  in
            Prims.strcat ") (" uu____6384  in
          Prims.strcat uu____6382 uu____6383  in
        Prims.strcat "MisMatch (" uu____6381
    | HeadMatch u ->
        let uu____6387 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6387
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___137_6392  ->
    match uu___137_6392 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6407 -> HeadMatch false
  
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
          let uu____6421 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6421 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6432 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6455 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6464 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6492 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6492
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6493 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6494 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6495 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6510 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6523 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6547) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6553,uu____6554) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6596) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6617;
             FStar_Syntax_Syntax.index = uu____6618;
             FStar_Syntax_Syntax.sort = t2;_},uu____6620)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6627 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6628 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6629 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6642 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6649 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6667 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6667
  
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
            let uu____6694 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6694
            then FullMatch
            else
              (let uu____6696 =
                 let uu____6705 =
                   let uu____6708 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6708  in
                 let uu____6709 =
                   let uu____6712 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6712  in
                 (uu____6705, uu____6709)  in
               MisMatch uu____6696)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6718),FStar_Syntax_Syntax.Tm_uinst (g,uu____6720)) ->
            let uu____6729 = head_matches env f g  in
            FStar_All.pipe_right uu____6729 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6732 = FStar_Const.eq_const c d  in
            if uu____6732
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6739),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6741)) ->
            let uu____6782 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6782
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6789),FStar_Syntax_Syntax.Tm_refine (y,uu____6791)) ->
            let uu____6800 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6800 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6802),uu____6803) ->
            let uu____6808 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6808 head_match
        | (uu____6809,FStar_Syntax_Syntax.Tm_refine (x,uu____6811)) ->
            let uu____6816 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6816 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6817,FStar_Syntax_Syntax.Tm_type
           uu____6818) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6819,FStar_Syntax_Syntax.Tm_arrow uu____6820) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6846),FStar_Syntax_Syntax.Tm_app (head',uu____6848))
            ->
            let uu____6889 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6889 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6891),uu____6892) ->
            let uu____6913 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6913 head_match
        | (uu____6914,FStar_Syntax_Syntax.Tm_app (head1,uu____6916)) ->
            let uu____6937 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6937 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6938,FStar_Syntax_Syntax.Tm_let
           uu____6939) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6964,FStar_Syntax_Syntax.Tm_match uu____6965) ->
            HeadMatch true
        | uu____7010 ->
            let uu____7015 =
              let uu____7024 = delta_depth_of_term env t11  in
              let uu____7027 = delta_depth_of_term env t21  in
              (uu____7024, uu____7027)  in
            MisMatch uu____7015
  
let head_matches_delta :
  'Auu____7044 .
    FStar_TypeChecker_Env.env ->
      'Auu____7044 ->
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
            (let uu____7093 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7093
             then
               let uu____7094 = FStar_Syntax_Print.term_to_string t  in
               let uu____7095 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7094 uu____7095
             else ());
            (let uu____7097 =
               let uu____7098 = FStar_Syntax_Util.un_uinst head1  in
               uu____7098.FStar_Syntax_Syntax.n  in
             match uu____7097 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7104 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7104 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7118 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7118
                        then
                          let uu____7119 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7119
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7121 ->
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
                      ((let uu____7132 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7132
                        then
                          let uu____7133 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7134 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7133
                            uu____7134
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7136 -> FStar_Pervasives_Native.None)
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
            (let uu____7274 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7274
             then
               let uu____7275 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7276 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7277 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7275
                 uu____7276 uu____7277
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7301 =
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
               match uu____7301 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7346 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7346 with
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
                  uu____7378),uu____7379)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7397 =
                      let uu____7406 = maybe_inline t11  in
                      let uu____7409 = maybe_inline t21  in
                      (uu____7406, uu____7409)  in
                    match uu____7397 with
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
                 (uu____7446,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7447))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7465 =
                      let uu____7474 = maybe_inline t11  in
                      let uu____7477 = maybe_inline t21  in
                      (uu____7474, uu____7477)  in
                    match uu____7465 with
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
             | MisMatch uu____7526 -> fail1 n_delta r t11 t21
             | uu____7535 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7548 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7548
           then
             let uu____7549 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7550 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7551 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7558 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7576 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7576
                    (fun uu____7610  ->
                       match uu____7610 with
                       | (t11,t21) ->
                           let uu____7617 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7618 =
                             let uu____7619 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7619  in
                           Prims.strcat uu____7617 uu____7618))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7549 uu____7550 uu____7551 uu____7558
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7631 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7631 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___138_7644  ->
    match uu___138_7644 with
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
      let uu___163_7681 = p  in
      let uu____7684 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7685 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___163_7681.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7684;
        FStar_TypeChecker_Common.relation =
          (uu___163_7681.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7685;
        FStar_TypeChecker_Common.element =
          (uu___163_7681.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___163_7681.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___163_7681.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___163_7681.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___163_7681.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___163_7681.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7699 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7699
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7704 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7726 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7726 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7734 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7734 with
           | (lh,lhs_args) ->
               let uu____7775 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7775 with
                | (rh,rhs_args) ->
                    let uu____7816 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7829,FStar_Syntax_Syntax.Tm_uvar uu____7830)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7911 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7934,uu____7935)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7952,FStar_Syntax_Syntax.Tm_uvar uu____7953)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7970,FStar_Syntax_Syntax.Tm_arrow uu____7971)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_8001 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_8001.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_8001.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_8001.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_8001.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_8001.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_8001.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_8001.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_8001.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_8001.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8004,FStar_Syntax_Syntax.Tm_type uu____8005)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_8023 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_8023.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_8023.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_8023.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_8023.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_8023.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_8023.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_8023.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_8023.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_8023.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8026,FStar_Syntax_Syntax.Tm_uvar uu____8027)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_8045 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_8045.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_8045.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_8045.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_8045.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_8045.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_8045.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_8045.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_8045.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_8045.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8048,FStar_Syntax_Syntax.Tm_uvar uu____8049)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8066,uu____8067)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8084,FStar_Syntax_Syntax.Tm_uvar uu____8085)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8102,uu____8103) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7816 with
                     | (rank,tp1) ->
                         let uu____8116 =
                           FStar_All.pipe_right
                             (let uu___165_8120 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___165_8120.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___165_8120.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___165_8120.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___165_8120.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___165_8120.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___165_8120.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___165_8120.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___165_8120.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___165_8120.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8116))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8126 =
            FStar_All.pipe_right
              (let uu___166_8130 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___166_8130.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___166_8130.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___166_8130.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___166_8130.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___166_8130.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___166_8130.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___166_8130.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___166_8130.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___166_8130.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8126)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8191 probs =
      match uu____8191 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8272 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8293 = rank wl.tcenv hd1  in
               (match uu____8293 with
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
                      (let uu____8352 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8356 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8356)
                          in
                       if uu____8352
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
          let uu____8424 = FStar_Syntax_Util.head_and_args t  in
          match uu____8424 with
          | (hd1,uu____8440) ->
              let uu____8461 =
                let uu____8462 = FStar_Syntax_Subst.compress hd1  in
                uu____8462.FStar_Syntax_Syntax.n  in
              (match uu____8461 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8466) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8500  ->
                           match uu____8500 with
                           | (y,uu____8506) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8520  ->
                                       match uu____8520 with
                                       | (x,uu____8526) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8527 -> false)
           in
        let uu____8528 = rank tcenv p  in
        match uu____8528 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8535 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8562 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8576 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8590 -> false
  
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
                        let uu____8642 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8642 with
                        | (k,uu____8648) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8658 -> false)))
            | uu____8659 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8711 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8717 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8717 = (Prims.parse_int "0")))
                           in
                        if uu____8711 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8733 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8739 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8739 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8733)
               in
            let uu____8740 = filter1 u12  in
            let uu____8743 = filter1 u22  in (uu____8740, uu____8743)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8772 = filter_out_common_univs us1 us2  in
                (match uu____8772 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8831 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8831 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8834 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8844 =
                          let uu____8845 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8846 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8845
                            uu____8846
                           in
                        UFailed uu____8844))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8870 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8870 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8896 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8896 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8899 ->
                let uu____8904 =
                  let uu____8905 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8906 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8905
                    uu____8906 msg
                   in
                UFailed uu____8904
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8907,uu____8908) ->
              let uu____8909 =
                let uu____8910 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8911 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8910 uu____8911
                 in
              failwith uu____8909
          | (FStar_Syntax_Syntax.U_unknown ,uu____8912) ->
              let uu____8913 =
                let uu____8914 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8915 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8914 uu____8915
                 in
              failwith uu____8913
          | (uu____8916,FStar_Syntax_Syntax.U_bvar uu____8917) ->
              let uu____8918 =
                let uu____8919 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8920 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8919 uu____8920
                 in
              failwith uu____8918
          | (uu____8921,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8922 =
                let uu____8923 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8924 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8923 uu____8924
                 in
              failwith uu____8922
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8948 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8948
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8962 = occurs_univ v1 u3  in
              if uu____8962
              then
                let uu____8963 =
                  let uu____8964 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8965 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8964 uu____8965
                   in
                try_umax_components u11 u21 uu____8963
              else
                (let uu____8967 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8967)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8979 = occurs_univ v1 u3  in
              if uu____8979
              then
                let uu____8980 =
                  let uu____8981 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8982 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8981 uu____8982
                   in
                try_umax_components u11 u21 uu____8980
              else
                (let uu____8984 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8984)
          | (FStar_Syntax_Syntax.U_max uu____8985,uu____8986) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8992 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8992
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8994,FStar_Syntax_Syntax.U_max uu____8995) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9001 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9001
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9003,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9004,FStar_Syntax_Syntax.U_name
             uu____9005) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9006) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9007) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9008,FStar_Syntax_Syntax.U_succ
             uu____9009) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9010,FStar_Syntax_Syntax.U_zero
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
      let uu____9110 = bc1  in
      match uu____9110 with
      | (bs1,mk_cod1) ->
          let uu____9154 = bc2  in
          (match uu____9154 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9265 = aux xs ys  in
                     (match uu____9265 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9348 =
                       let uu____9355 = mk_cod1 xs  in ([], uu____9355)  in
                     let uu____9358 =
                       let uu____9365 = mk_cod2 ys  in ([], uu____9365)  in
                     (uu____9348, uu____9358)
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
                  let uu____9435 =
                    let uu____9436 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9436 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9435
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9441 = has_type_guard t1 t2  in (uu____9441, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9442 = has_type_guard t2 t1  in (uu____9442, wl)
  
let is_flex_pat :
  'Auu____9451 'Auu____9452 'Auu____9453 .
    ('Auu____9451,'Auu____9452,'Auu____9453 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___139_9466  ->
    match uu___139_9466 with
    | (uu____9475,uu____9476,[]) -> true
    | uu____9479 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9510 = f  in
      match uu____9510 with
      | (uu____9517,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9518;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9519;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9522;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9523;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9524;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9576  ->
                 match uu____9576 with
                 | (y,uu____9582) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9704 =
                  let uu____9717 =
                    let uu____9720 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9720  in
                  ((FStar_List.rev pat_binders), uu____9717)  in
                FStar_Pervasives_Native.Some uu____9704
            | (uu____9747,[]) ->
                let uu____9770 =
                  let uu____9783 =
                    let uu____9786 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9786  in
                  ((FStar_List.rev pat_binders), uu____9783)  in
                FStar_Pervasives_Native.Some uu____9770
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9851 =
                  let uu____9852 = FStar_Syntax_Subst.compress a  in
                  uu____9852.FStar_Syntax_Syntax.n  in
                (match uu____9851 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9870 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9870
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___167_9891 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___167_9891.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___167_9891.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9895 =
                            let uu____9896 =
                              let uu____9903 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9903)  in
                            FStar_Syntax_Syntax.NT uu____9896  in
                          [uu____9895]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___168_9915 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___168_9915.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___168_9915.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9916 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9944 =
                  let uu____9957 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9957  in
                (match uu____9944 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10020 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10047 ->
               let uu____10048 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10048 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10324 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10324
       then
         let uu____10325 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10325
       else ());
      (let uu____10327 = next_prob probs  in
       match uu____10327 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___169_10354 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___169_10354.wl_deferred);
               ctr = (uu___169_10354.ctr);
               defer_ok = (uu___169_10354.defer_ok);
               smt_ok = (uu___169_10354.smt_ok);
               tcenv = (uu___169_10354.tcenv);
               wl_implicits = (uu___169_10354.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10361 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10361
                then
                  let uu____10362 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10362
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
                          (let uu___170_10367 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___170_10367.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___170_10367.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___170_10367.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___170_10367.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___170_10367.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___170_10367.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___170_10367.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___170_10367.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___170_10367.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10389 ->
                let uu____10398 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10457  ->
                          match uu____10457 with
                          | (c,uu____10465,uu____10466) -> c < probs.ctr))
                   in
                (match uu____10398 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10507 =
                            let uu____10512 =
                              FStar_List.map
                                (fun uu____10527  ->
                                   match uu____10527 with
                                   | (uu____10538,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10512, (probs.wl_implicits))  in
                          Success uu____10507
                      | uu____10541 ->
                          let uu____10550 =
                            let uu___171_10551 = probs  in
                            let uu____10552 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10571  ->
                                      match uu____10571 with
                                      | (uu____10578,uu____10579,y) -> y))
                               in
                            {
                              attempting = uu____10552;
                              wl_deferred = rest;
                              ctr = (uu___171_10551.ctr);
                              defer_ok = (uu___171_10551.defer_ok);
                              smt_ok = (uu___171_10551.smt_ok);
                              tcenv = (uu___171_10551.tcenv);
                              wl_implicits = (uu___171_10551.wl_implicits)
                            }  in
                          solve env uu____10550))))

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
            let uu____10586 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10586 with
            | USolved wl1 ->
                let uu____10588 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10588
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
                  let uu____10640 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10640 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10643 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10655;
                  FStar_Syntax_Syntax.vars = uu____10656;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10659;
                  FStar_Syntax_Syntax.vars = uu____10660;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10672,uu____10673) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10680,FStar_Syntax_Syntax.Tm_uinst uu____10681) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10688 -> USolved wl

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
            ((let uu____10698 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10698
              then
                let uu____10699 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10699 msg
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
              let uu____10784 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10784 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10836 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10836
               then
                 let uu____10837 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10838 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                   uu____10837 uu____10838
               else ());
              (let uu____10840 = head_matches_delta env1 () t1 t2  in
               match uu____10840 with
               | (mr,ts1) ->
                   (match mr with
                    | HeadMatch (true ) ->
                        let uu____10885 = eq_prob t1 t2 wl2  in
                        (match uu____10885 with | (p,wl3) -> (t1, [p], wl3))
                    | MisMatch uu____10906 ->
                        let uu____10915 = eq_prob t1 t2 wl2  in
                        (match uu____10915 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch (false ) ->
                        let uu____10964 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10979 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10980 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10979, uu____10980)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10985 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10986 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10985, uu____10986)
                           in
                        (match uu____10964 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____11017 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____11017 with
                               | (t1_hd,t1_args) ->
                                   let uu____11056 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____11056 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____11110 =
                                             let uu____11117 =
                                               let uu____11126 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____11126 :: t1_args  in
                                             let uu____11139 =
                                               let uu____11146 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____11146 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____11187  ->
                                                  fun uu____11188  ->
                                                    fun uu____11189  ->
                                                      match (uu____11187,
                                                              uu____11188,
                                                              uu____11189)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____11231),
                                                         (a2,uu____11233)) ->
                                                          let uu____11258 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____11258
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____11117
                                               uu____11139
                                              in
                                           match uu____11110 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___172_11284 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___172_11284.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___172_11284.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11300 =
                                                 solve env1 wl'  in
                                               (match uu____11300 with
                                                | Success (uu____11303,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___173_11307 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___173_11307.attempting);
                                                           wl_deferred =
                                                             (uu___173_11307.wl_deferred);
                                                           ctr =
                                                             (uu___173_11307.ctr);
                                                           defer_ok =
                                                             (uu___173_11307.defer_ok);
                                                           smt_ok =
                                                             (uu___173_11307.smt_ok);
                                                           tcenv =
                                                             (uu___173_11307.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11316 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11348 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11348 with
                               | (t1_base,p1_opt) ->
                                   let uu____11395 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11395 with
                                    | (t2_base,p2_opt) ->
                                        let combine_refinements t_base
                                          p1_opt1 p2_opt1 =
                                          let refine1 x t =
                                            let uu____11505 =
                                              FStar_Syntax_Util.is_t_true t
                                               in
                                            if uu____11505
                                            then x.FStar_Syntax_Syntax.sort
                                            else FStar_Syntax_Util.refine x t
                                             in
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
                                              let uu____11553 =
                                                op phi11 phi21  in
                                              refine1 x1 uu____11553
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
                                              let uu____11583 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              refine1 x1 uu____11583
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
                                              let uu____11613 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              refine1 x1 uu____11613
                                          | uu____11616 -> t_base  in
                                        let uu____11633 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11633 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11647 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11647, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11654 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11654 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11701 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11701 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11748 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11748
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
                             let uu____11772 = combine t11 t21 wl2  in
                             (match uu____11772 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11805 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11805
                                    then
                                      let uu____11806 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11806
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11845 ts1 =
              match uu____11845 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11908 = pairwise out t wl2  in
                       (match uu____11908 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11944 =
              let uu____11955 = FStar_List.hd ts  in (uu____11955, [], wl1)
               in
            let uu____11964 = FStar_List.tl ts  in
            aux uu____11944 uu____11964  in
          let uu____11971 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11971 with
          | (this_flex,this_rigid) ->
              let uu____11995 =
                let uu____11996 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11996.FStar_Syntax_Syntax.n  in
              (match uu____11995 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____12017 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____12017
                   then
                     let uu____12018 = destruct_flex_t this_flex wl  in
                     (match uu____12018 with
                      | (flex,wl1) ->
                          let uu____12025 = quasi_pattern env flex  in
                          (match uu____12025 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____12043 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____12043
                                 then
                                   let uu____12044 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____12044
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
                             ((let uu___174_12049 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___174_12049.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___174_12049.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___174_12049.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___174_12049.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___174_12049.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___174_12049.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___174_12049.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___174_12049.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___174_12049.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____12050 ->
                   ((let uu____12052 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____12052
                     then
                       let uu____12053 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____12053
                     else ());
                    (let uu____12055 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____12055 with
                     | (u,_args) ->
                         let uu____12092 =
                           let uu____12093 = FStar_Syntax_Subst.compress u
                              in
                           uu____12093.FStar_Syntax_Syntax.n  in
                         (match uu____12092 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____12124 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____12124 with
                                | (u',uu____12140) ->
                                    let uu____12161 =
                                      let uu____12162 = whnf env u'  in
                                      uu____12162.FStar_Syntax_Syntax.n  in
                                    (match uu____12161 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____12187 -> false)
                                 in
                              let uu____12188 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___140_12211  ->
                                        match uu___140_12211 with
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
                                             | uu____12220 -> false)
                                        | uu____12223 -> false))
                                 in
                              (match uu____12188 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____12237 = whnf env this_rigid
                                        in
                                     let uu____12238 =
                                       FStar_List.collect
                                         (fun uu___141_12244  ->
                                            match uu___141_12244 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____12250 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____12250]
                                            | uu____12252 -> []) bounds_probs
                                        in
                                     uu____12237 :: uu____12238  in
                                   let uu____12253 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj_simp
                                        else FStar_Syntax_Util.mk_disj_simp)
                                       bounds_typs env wl
                                      in
                                   (match uu____12253 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____12284 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____12299 =
                                              let uu____12300 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____12300.FStar_Syntax_Syntax.n
                                               in
                                            match uu____12299 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____12312 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____12312)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____12321 -> bound  in
                                          let uu____12322 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____12322)  in
                                        (match uu____12284 with
                                         | (bound_typ,(eq_prob,wl')) ->
                                             ((let uu____12350 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____12350
                                               then
                                                 let wl'1 =
                                                   let uu___175_12352 = wl1
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___175_12352.wl_deferred);
                                                     ctr =
                                                       (uu___175_12352.ctr);
                                                     defer_ok =
                                                       (uu___175_12352.defer_ok);
                                                     smt_ok =
                                                       (uu___175_12352.smt_ok);
                                                     tcenv =
                                                       (uu___175_12352.tcenv);
                                                     wl_implicits =
                                                       (uu___175_12352.wl_implicits)
                                                   }  in
                                                 let uu____12353 =
                                                   wl_to_string wl'1  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____12353
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____12356 =
                                                 solve_t env eq_prob
                                                   (let uu___176_12358 = wl'
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___176_12358.wl_deferred);
                                                      ctr =
                                                        (uu___176_12358.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___176_12358.smt_ok);
                                                      tcenv =
                                                        (uu___176_12358.tcenv);
                                                      wl_implicits =
                                                        (uu___176_12358.wl_implicits)
                                                    })
                                                  in
                                               match uu____12356 with
                                               | Success uu____12359 ->
                                                   let wl2 =
                                                     let uu___177_12365 = wl'
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___177_12365.wl_deferred);
                                                       ctr =
                                                         (uu___177_12365.ctr);
                                                       defer_ok =
                                                         (uu___177_12365.defer_ok);
                                                       smt_ok =
                                                         (uu___177_12365.smt_ok);
                                                       tcenv =
                                                         (uu___177_12365.tcenv);
                                                       wl_implicits =
                                                         (uu___177_12365.wl_implicits)
                                                     }  in
                                                   let g =
                                                     FStar_List.fold_left
                                                       (fun g  ->
                                                          fun p  ->
                                                            FStar_Syntax_Util.mk_conj
                                                              g (p_guard p))
                                                       eq_prob.FStar_TypeChecker_Common.logical_guard
                                                       sub_probs
                                                      in
                                                   let wl3 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       (FStar_Pervasives_Native.Some
                                                          g) [] wl2
                                                      in
                                                   let uu____12380 =
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
                                                    (let uu____12392 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12392
                                                     then
                                                       let uu____12393 =
                                                         let uu____12394 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12394
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12393
                                                     else ());
                                                    (let uu____12400 =
                                                       let uu____12415 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12415)
                                                        in
                                                     match uu____12400 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12437))
                                                         ->
                                                         let uu____12462 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12462
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
                                                         let uu____12501 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12501
                                                          with
                                                          | (eq_prob1,wl2) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl2 tp x
                                                                  phi
                                                                 in
                                                              let wl3 =
                                                                let uu____12518
                                                                  =
                                                                  let uu____12523
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12523
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12518
                                                                  [] wl2
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl3))
                                                     | uu____12528 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12543 when flip ->
                              let uu____12544 =
                                let uu____12545 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12546 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12545 uu____12546
                                 in
                              failwith uu____12544
                          | uu____12547 ->
                              let uu____12548 =
                                let uu____12549 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12550 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12549 uu____12550
                                 in
                              failwith uu____12548))))

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
                      (fun uu____12578  ->
                         match uu____12578 with
                         | (x,i) ->
                             let uu____12589 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12589, i)) bs_lhs
                     in
                  let uu____12590 = lhs  in
                  match uu____12590 with
                  | (uu____12591,u_lhs,uu____12593) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12706 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12716 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12716, univ)
                             in
                          match uu____12706 with
                          | (k,univ) ->
                              let uu____12725 =
                                let uu____12732 =
                                  let uu____12735 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12735
                                   in
                                copy_uvar u_lhs uu____12732 wl2  in
                              (match uu____12725 with
                               | (uu____12748,u,wl3) ->
                                   let uu____12751 =
                                     let uu____12754 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12754
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12751, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12790 =
                              let uu____12803 =
                                let uu____12812 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12812 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12858  ->
                                   fun uu____12859  ->
                                     match (uu____12858, uu____12859) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12950 =
                                           let uu____12957 =
                                             let uu____12960 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12960
                                              in
                                           copy_uvar u_lhs uu____12957 wl2
                                            in
                                         (match uu____12950 with
                                          | (uu____12983,t_a,wl3) ->
                                              let uu____12986 =
                                                let uu____12993 =
                                                  let uu____12996 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12996
                                                   in
                                                copy_uvar u_lhs uu____12993
                                                  wl3
                                                 in
                                              (match uu____12986 with
                                               | (uu____13011,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12803
                                ([], wl1)
                               in
                            (match uu____12790 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___178_13072 = ct  in
                                   let uu____13073 =
                                     let uu____13076 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13076
                                      in
                                   let uu____13091 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___178_13072.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___178_13072.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13073;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13091;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___178_13072.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___179_13109 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___179_13109.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___179_13109.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13112 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13112 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13166 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13166 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13183 =
                                          let uu____13188 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13188)  in
                                        TERM uu____13183  in
                                      let uu____13189 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13189 with
                                       | (sub_prob,wl3) ->
                                           let uu____13200 =
                                             let uu____13201 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13201
                                              in
                                           solve env uu____13200))
                             | (x,imp)::formals2 ->
                                 let uu____13215 =
                                   let uu____13222 =
                                     let uu____13225 =
                                       let uu____13228 =
                                         let uu____13229 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____13229
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____13228
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____13225
                                      in
                                   copy_uvar u_lhs uu____13222 wl1  in
                                 (match uu____13215 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____13253 =
                                          let uu____13256 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13256
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13253 t_y
                                         in
                                      let uu____13257 =
                                        let uu____13260 =
                                          let uu____13263 =
                                            let uu____13264 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13264, imp)  in
                                          [uu____13263]  in
                                        FStar_List.append bs_terms
                                          uu____13260
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13257 formals2 wl2)
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
              (let uu____13306 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13306
               then
                 let uu____13307 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13308 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13307 (rel_to_string (p_rel orig)) uu____13308
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13413 = rhs wl1 scope env1 subst1  in
                     (match uu____13413 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13433 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13433
                            then
                              let uu____13434 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13434
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___180_13488 = hd1  in
                       let uu____13489 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___180_13488.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___180_13488.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13489
                       }  in
                     let hd21 =
                       let uu___181_13493 = hd2  in
                       let uu____13494 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___181_13493.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___181_13493.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13494
                       }  in
                     let uu____13497 =
                       let uu____13502 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13502
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13497 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13521 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13521
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13525 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13525 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13580 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13580
                                  in
                               ((let uu____13592 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13592
                                 then
                                   let uu____13593 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13594 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13593
                                     uu____13594
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13621 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13650 = aux wl [] env [] bs1 bs2  in
               match uu____13650 with
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
        (let uu____13701 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13701 wl)

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
              let uu____13715 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13715 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13745 = lhs1  in
              match uu____13745 with
              | (uu____13748,ctx_u,uu____13750) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13756 ->
                        let uu____13757 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13757 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13804 = quasi_pattern env1 lhs1  in
              match uu____13804 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13834) ->
                  let uu____13839 = lhs1  in
                  (match uu____13839 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13853 = occurs_check ctx_u rhs1  in
                       (match uu____13853 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13895 =
                                let uu____13902 =
                                  let uu____13903 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13903
                                   in
                                FStar_Util.Inl uu____13902  in
                              (uu____13895, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13923 =
                                 let uu____13924 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13924  in
                               if uu____13923
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13944 =
                                    let uu____13951 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13951  in
                                  let uu____13956 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13944, uu____13956)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14018  ->
                     match uu____14018 with
                     | (x,i) ->
                         let uu____14029 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14029, i)) bs_lhs
                 in
              let uu____14030 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14030 with
              | (rhs_hd,args) ->
                  let uu____14067 = FStar_Util.prefix args  in
                  (match uu____14067 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14125 = lhs1  in
                       (match uu____14125 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14129 =
                              let uu____14140 =
                                let uu____14147 =
                                  let uu____14150 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14150
                                   in
                                copy_uvar u_lhs uu____14147 wl1  in
                              match uu____14140 with
                              | (uu____14171,t_last_arg,wl2) ->
                                  let uu____14174 =
                                    let uu____14181 =
                                      let uu____14184 =
                                        let uu____14191 =
                                          let uu____14198 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____14198]  in
                                        FStar_List.append bs_lhs uu____14191
                                         in
                                      let uu____14215 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____14184
                                        uu____14215
                                       in
                                    copy_uvar u_lhs uu____14181 wl2  in
                                  (match uu____14174 with
                                   | (uu____14228,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14234 =
                                         let uu____14241 =
                                           let uu____14244 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____14244
                                            in
                                         copy_uvar u_lhs uu____14241 wl3  in
                                       (match uu____14234 with
                                        | (uu____14257,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14129 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14281 =
                                     let uu____14282 =
                                       let uu____14287 =
                                         let uu____14288 =
                                           let uu____14291 =
                                             let uu____14296 =
                                               let uu____14297 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14297]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14296
                                              in
                                           uu____14291
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14288
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14287)  in
                                     TERM uu____14282  in
                                   [uu____14281]  in
                                 let uu____14318 =
                                   let uu____14325 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14325 with
                                   | (p1,wl3) ->
                                       let uu____14342 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14342 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14318 with
                                  | (sub_probs,wl3) ->
                                      let uu____14369 =
                                        let uu____14370 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14370  in
                                      solve env1 uu____14369))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14403 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14403 with
                | (uu____14418,args) ->
                    (match args with | [] -> false | uu____14446 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14461 =
                  let uu____14462 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14462.FStar_Syntax_Syntax.n  in
                match uu____14461 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14465 -> true
                | uu____14478 -> false  in
              let uu____14479 = quasi_pattern env1 lhs1  in
              match uu____14479 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14490 =
                    let uu____14491 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14491
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14490
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14498 = is_app rhs1  in
                  if uu____14498
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14500 = is_arrow rhs1  in
                     if uu____14500
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14502 =
                          let uu____14503 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14503
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14502))
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
                let uu____14506 = lhs  in
                (match uu____14506 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14510 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14510 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14525 =
                              let uu____14528 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14528
                               in
                            FStar_All.pipe_right uu____14525
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14543 = occurs_check ctx_uv rhs1  in
                          (match uu____14543 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14565 =
                                   let uu____14566 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14566
                                    in
                                 giveup_or_defer env orig wl uu____14565
                               else
                                 (let uu____14568 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14568
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14573 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14573
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14575 =
                                         let uu____14576 =
                                           names_to_string1 fvs2  in
                                         let uu____14577 =
                                           names_to_string1 fvs1  in
                                         let uu____14578 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14576 uu____14577
                                           uu____14578
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14575)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14584 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14588 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14588 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14611 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14611
                             | (FStar_Util.Inl msg,uu____14613) ->
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
                  (let uu____14642 =
                     let uu____14659 = quasi_pattern env lhs  in
                     let uu____14666 = quasi_pattern env rhs  in
                     (uu____14659, uu____14666)  in
                   match uu____14642 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14709 = lhs  in
                       (match uu____14709 with
                        | ({ FStar_Syntax_Syntax.n = uu____14710;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14712;_},u_lhs,uu____14714)
                            ->
                            let uu____14717 = rhs  in
                            (match uu____14717 with
                             | (uu____14718,u_rhs,uu____14720) ->
                                 let uu____14721 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14721
                                 then
                                   let uu____14722 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14722
                                 else
                                   (let uu____14724 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14724 with
                                    | (sub_prob,wl1) ->
                                        let uu____14735 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14735 with
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
                                             let uu____14763 =
                                               let uu____14770 =
                                                 let uu____14773 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14773
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
                                                 uu____14770
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14763 with
                                              | (uu____14776,w,wl2) ->
                                                  let w_app =
                                                    let uu____14782 =
                                                      let uu____14787 =
                                                        FStar_List.map
                                                          (fun uu____14796 
                                                             ->
                                                             match uu____14796
                                                             with
                                                             | (z,uu____14802)
                                                                 ->
                                                                 let uu____14803
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14803)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14787
                                                       in
                                                    uu____14782
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14807 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14807
                                                    then
                                                      let uu____14808 =
                                                        let uu____14811 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14812 =
                                                          let uu____14815 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14816 =
                                                            let uu____14819 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14820 =
                                                              let uu____14823
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14828
                                                                =
                                                                let uu____14831
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14836
                                                                  =
                                                                  let uu____14839
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14839]
                                                                   in
                                                                uu____14831
                                                                  ::
                                                                  uu____14836
                                                                 in
                                                              uu____14823 ::
                                                                uu____14828
                                                               in
                                                            uu____14819 ::
                                                              uu____14820
                                                             in
                                                          uu____14815 ::
                                                            uu____14816
                                                           in
                                                        uu____14811 ::
                                                          uu____14812
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14808
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14845 =
                                                          let uu____14850 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14850)
                                                           in
                                                        TERM uu____14845  in
                                                      let uu____14851 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14851
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14856 =
                                                             let uu____14861
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
                                                               uu____14861)
                                                              in
                                                           TERM uu____14856
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14862 =
                                                      let uu____14863 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14863
                                                       in
                                                    solve env uu____14862)))))))
                   | uu____14864 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14928 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14928
            then
              let uu____14929 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14930 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14931 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14932 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14929 uu____14930 uu____14931 uu____14932
            else ());
           (let uu____14936 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14936
            then
              let uu____14937 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14938 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14939 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14940 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14937 uu____14938 uu____14939 uu____14940
            else ());
           (let uu____14942 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14942 with
            | (head1,args1) ->
                let uu____14979 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14979 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15033 =
                         let uu____15034 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15035 = args_to_string args1  in
                         let uu____15036 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15037 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15034 uu____15035 uu____15036 uu____15037
                          in
                       giveup env1 uu____15033 orig
                     else
                       (let uu____15039 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15045 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15045 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15039
                        then
                          let uu____15046 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____15046 with
                          | USolved wl2 ->
                              let uu____15048 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____15048
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____15052 = base_and_refinement env1 t1  in
                           match uu____15052 with
                           | (base1,refinement1) ->
                               let uu____15077 = base_and_refinement env1 t2
                                  in
                               (match uu____15077 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15134 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15134 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15138 =
                                                FStar_List.fold_right2
                                                  (fun uu____15171  ->
                                                     fun uu____15172  ->
                                                       fun uu____15173  ->
                                                         match (uu____15171,
                                                                 uu____15172,
                                                                 uu____15173)
                                                         with
                                                         | ((a,uu____15209),
                                                            (a',uu____15211),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15232
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15232
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15138 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15260 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15260
                                                     then
                                                       let uu____15261 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15261
                                                     else ());
                                                    (let formula =
                                                       let uu____15266 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15266
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     solve env1
                                                       (attempt subprobs wl4)))))
                                     | uu____15274 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___182_15314 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___182_15314.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___182_15314.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___182_15314.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___182_15314.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___182_15314.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___182_15314.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___182_15314.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___182_15314.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15352 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15352
            then
              let uu____15353 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15354 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15355 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15356 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15353 uu____15354 uu____15355 uu____15356
            else ());
           (let uu____15358 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15358 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15389,uu____15390) ->
                     let rec may_relate head3 =
                       let uu____15417 =
                         let uu____15418 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15418.FStar_Syntax_Syntax.n  in
                       match uu____15417 with
                       | FStar_Syntax_Syntax.Tm_name uu____15421 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15422 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15445;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15446;
                             FStar_Syntax_Syntax.fv_qual = uu____15447;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15450;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15451;
                             FStar_Syntax_Syntax.fv_qual = uu____15452;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15456,uu____15457) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15499) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15505) ->
                           may_relate t
                       | uu____15510 -> false  in
                     let uu____15511 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15511
                     then
                       let uu____15512 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15512 with
                        | (guard,wl2) ->
                            let uu____15519 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15519)
                     else
                       (let uu____15521 =
                          let uu____15522 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15523 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15522 uu____15523
                           in
                        giveup env1 uu____15521 orig)
                 | (HeadMatch (true ),uu____15524) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____15537 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15537 with
                        | (guard,wl2) ->
                            let uu____15544 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15544)
                     else
                       (let uu____15546 =
                          let uu____15547 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____15548 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____15547 uu____15548
                           in
                        giveup env1 uu____15546 orig)
                 | (uu____15549,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___183_15563 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___183_15563.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___183_15563.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___183_15563.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___183_15563.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___183_15563.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___183_15563.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___183_15563.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___183_15563.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15587 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15587
          then
            let uu____15588 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15588
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15593 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15593
              then
                let uu____15594 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15595 =
                  let uu____15596 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15597 =
                    let uu____15598 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15598  in
                  Prims.strcat uu____15596 uu____15597  in
                let uu____15599 =
                  let uu____15600 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15601 =
                    let uu____15602 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15602  in
                  Prims.strcat uu____15600 uu____15601  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15594
                  uu____15595 uu____15599
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15605,uu____15606) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15631,FStar_Syntax_Syntax.Tm_delayed uu____15632) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15657,uu____15658) ->
                  let uu____15685 =
                    let uu___184_15686 = problem  in
                    let uu____15687 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___184_15686.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15687;
                      FStar_TypeChecker_Common.relation =
                        (uu___184_15686.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___184_15686.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___184_15686.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___184_15686.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___184_15686.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___184_15686.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___184_15686.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___184_15686.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15685 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15688,uu____15689) ->
                  let uu____15696 =
                    let uu___185_15697 = problem  in
                    let uu____15698 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___185_15697.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15698;
                      FStar_TypeChecker_Common.relation =
                        (uu___185_15697.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___185_15697.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___185_15697.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___185_15697.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___185_15697.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___185_15697.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___185_15697.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___185_15697.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15696 wl
              | (uu____15699,FStar_Syntax_Syntax.Tm_ascribed uu____15700) ->
                  let uu____15727 =
                    let uu___186_15728 = problem  in
                    let uu____15729 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___186_15728.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___186_15728.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___186_15728.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15729;
                      FStar_TypeChecker_Common.element =
                        (uu___186_15728.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___186_15728.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___186_15728.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___186_15728.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___186_15728.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___186_15728.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15727 wl
              | (uu____15730,FStar_Syntax_Syntax.Tm_meta uu____15731) ->
                  let uu____15738 =
                    let uu___187_15739 = problem  in
                    let uu____15740 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___187_15739.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___187_15739.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___187_15739.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15740;
                      FStar_TypeChecker_Common.element =
                        (uu___187_15739.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___187_15739.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___187_15739.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___187_15739.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___187_15739.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___187_15739.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15738 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15742),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15744)) ->
                  let uu____15753 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15753
              | (FStar_Syntax_Syntax.Tm_bvar uu____15754,uu____15755) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15756,FStar_Syntax_Syntax.Tm_bvar uu____15757) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___142_15816 =
                    match uu___142_15816 with
                    | [] -> c
                    | bs ->
                        let uu____15838 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15838
                     in
                  let uu____15847 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15847 with
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
                                    let uu____15970 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15970
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
                  let mk_t t l uu___143_16045 =
                    match uu___143_16045 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____16079 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____16079 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16198 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16199 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16198
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16199 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16200,uu____16201) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16228 -> true
                    | uu____16245 -> false  in
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
                      (let uu____16298 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___188_16306 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___188_16306.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___188_16306.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___188_16306.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___188_16306.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___188_16306.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___188_16306.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___188_16306.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___188_16306.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___188_16306.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___188_16306.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___188_16306.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___188_16306.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___188_16306.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___188_16306.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___188_16306.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___188_16306.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___188_16306.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___188_16306.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___188_16306.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___188_16306.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___188_16306.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___188_16306.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___188_16306.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___188_16306.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___188_16306.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___188_16306.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___188_16306.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___188_16306.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___188_16306.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___188_16306.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___188_16306.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___188_16306.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___188_16306.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___188_16306.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___188_16306.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___188_16306.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16298 with
                       | (uu____16309,ty,uu____16311) ->
                           let uu____16312 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16312)
                     in
                  let uu____16313 =
                    let uu____16330 = maybe_eta t1  in
                    let uu____16337 = maybe_eta t2  in
                    (uu____16330, uu____16337)  in
                  (match uu____16313 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___189_16379 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___189_16379.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___189_16379.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___189_16379.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___189_16379.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___189_16379.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___189_16379.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___189_16379.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___189_16379.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16400 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16400
                       then
                         let uu____16401 = destruct_flex_t not_abs wl  in
                         (match uu____16401 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16416 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16416.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16416.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16416.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16416.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16416.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16416.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16416.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16416.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16438 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16438
                       then
                         let uu____16439 = destruct_flex_t not_abs wl  in
                         (match uu____16439 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16454 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16454.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16454.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16454.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16454.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16454.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16454.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16454.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16454.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16456 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16473,FStar_Syntax_Syntax.Tm_abs uu____16474) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16501 -> true
                    | uu____16518 -> false  in
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
                      (let uu____16571 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___188_16579 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___188_16579.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___188_16579.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___188_16579.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___188_16579.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___188_16579.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___188_16579.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___188_16579.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___188_16579.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___188_16579.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___188_16579.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___188_16579.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___188_16579.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___188_16579.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___188_16579.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___188_16579.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___188_16579.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___188_16579.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___188_16579.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___188_16579.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___188_16579.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___188_16579.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___188_16579.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___188_16579.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___188_16579.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___188_16579.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___188_16579.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___188_16579.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___188_16579.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___188_16579.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___188_16579.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___188_16579.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___188_16579.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___188_16579.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___188_16579.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___188_16579.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___188_16579.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16571 with
                       | (uu____16582,ty,uu____16584) ->
                           let uu____16585 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16585)
                     in
                  let uu____16586 =
                    let uu____16603 = maybe_eta t1  in
                    let uu____16610 = maybe_eta t2  in
                    (uu____16603, uu____16610)  in
                  (match uu____16586 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___189_16652 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___189_16652.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___189_16652.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___189_16652.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___189_16652.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___189_16652.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___189_16652.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___189_16652.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___189_16652.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16673 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16673
                       then
                         let uu____16674 = destruct_flex_t not_abs wl  in
                         (match uu____16674 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16689 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16689.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16689.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16689.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16689.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16689.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16689.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16689.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16689.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16711 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16711
                       then
                         let uu____16712 = destruct_flex_t not_abs wl  in
                         (match uu____16712 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16727 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16727.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16727.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16727.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16727.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16727.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16727.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16727.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16727.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16729 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16761 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16761) &&
                       (let uu____16765 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16765))
                      &&
                      (let uu____16772 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16772 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___144_16784 =
                             match uu___144_16784 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16785 -> true
                             | uu____16786 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16787 -> false)
                     in
                  let uu____16788 = as_refinement should_delta env wl t1  in
                  (match uu____16788 with
                   | (x11,phi1) ->
                       let uu____16801 = as_refinement should_delta env wl t2
                          in
                       (match uu____16801 with
                        | (x21,phi21) ->
                            let uu____16814 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16814 with
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
                                   let uu____16880 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16880
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16892 =
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
                                   (let uu____16906 =
                                      let uu____16907 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16907  in
                                    Prims.op_Negation uu____16906) ||
                                     (let uu____16911 =
                                        let uu____16912 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16912
                                         in
                                      Prims.op_Negation uu____16911)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16915 =
                                     let uu____16920 =
                                       let uu____16927 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16927]  in
                                     mk_t_problem wl1 uu____16920 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16915 with
                                    | (ref_prob,wl2) ->
                                        let uu____16942 =
                                          solve env1
                                            (let uu___191_16944 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___191_16944.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___191_16944.smt_ok);
                                               tcenv = (uu___191_16944.tcenv);
                                               wl_implicits =
                                                 (uu___191_16944.wl_implicits)
                                             })
                                           in
                                        (match uu____16942 with
                                         | Failed (prob,msg) ->
                                             if
                                               ((Prims.op_Negation
                                                   env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                  && has_uvars)
                                                 ||
                                                 (Prims.op_Negation
                                                    wl2.smt_ok)
                                             then giveup env1 msg prob
                                             else fallback ()
                                         | Success uu____16954 ->
                                             let guard =
                                               let uu____16962 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16962
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___192_16971 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___192_16971.attempting);
                                                 wl_deferred =
                                                   (uu___192_16971.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___192_16971.defer_ok);
                                                 smt_ok =
                                                   (uu___192_16971.smt_ok);
                                                 tcenv =
                                                   (uu___192_16971.tcenv);
                                                 wl_implicits =
                                                   (uu___192_16971.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16973,FStar_Syntax_Syntax.Tm_uvar uu____16974) ->
                  let uu____17003 = destruct_flex_t t1 wl  in
                  (match uu____17003 with
                   | (f1,wl1) ->
                       let uu____17010 = destruct_flex_t t2 wl1  in
                       (match uu____17010 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17017;
                    FStar_Syntax_Syntax.pos = uu____17018;
                    FStar_Syntax_Syntax.vars = uu____17019;_},uu____17020),FStar_Syntax_Syntax.Tm_uvar
                 uu____17021) ->
                  let uu____17070 = destruct_flex_t t1 wl  in
                  (match uu____17070 with
                   | (f1,wl1) ->
                       let uu____17077 = destruct_flex_t t2 wl1  in
                       (match uu____17077 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17084,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17085;
                    FStar_Syntax_Syntax.pos = uu____17086;
                    FStar_Syntax_Syntax.vars = uu____17087;_},uu____17088))
                  ->
                  let uu____17137 = destruct_flex_t t1 wl  in
                  (match uu____17137 with
                   | (f1,wl1) ->
                       let uu____17144 = destruct_flex_t t2 wl1  in
                       (match uu____17144 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17151;
                    FStar_Syntax_Syntax.pos = uu____17152;
                    FStar_Syntax_Syntax.vars = uu____17153;_},uu____17154),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17155;
                    FStar_Syntax_Syntax.pos = uu____17156;
                    FStar_Syntax_Syntax.vars = uu____17157;_},uu____17158))
                  ->
                  let uu____17227 = destruct_flex_t t1 wl  in
                  (match uu____17227 with
                   | (f1,wl1) ->
                       let uu____17234 = destruct_flex_t t2 wl1  in
                       (match uu____17234 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____17241,uu____17242) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17257 = destruct_flex_t t1 wl  in
                  (match uu____17257 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17264;
                    FStar_Syntax_Syntax.pos = uu____17265;
                    FStar_Syntax_Syntax.vars = uu____17266;_},uu____17267),uu____17268)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17303 = destruct_flex_t t1 wl  in
                  (match uu____17303 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17310,FStar_Syntax_Syntax.Tm_uvar uu____17311) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17326,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17327;
                    FStar_Syntax_Syntax.pos = uu____17328;
                    FStar_Syntax_Syntax.vars = uu____17329;_},uu____17330))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17365,FStar_Syntax_Syntax.Tm_arrow uu____17366) ->
                  solve_t' env
                    (let uu___193_17394 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___193_17394.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___193_17394.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___193_17394.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___193_17394.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___193_17394.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___193_17394.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___193_17394.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___193_17394.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___193_17394.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17395;
                    FStar_Syntax_Syntax.pos = uu____17396;
                    FStar_Syntax_Syntax.vars = uu____17397;_},uu____17398),FStar_Syntax_Syntax.Tm_arrow
                 uu____17399) ->
                  solve_t' env
                    (let uu___193_17447 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___193_17447.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___193_17447.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___193_17447.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___193_17447.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___193_17447.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___193_17447.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___193_17447.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___193_17447.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___193_17447.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17448,FStar_Syntax_Syntax.Tm_uvar uu____17449) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____17464,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17465;
                    FStar_Syntax_Syntax.pos = uu____17466;
                    FStar_Syntax_Syntax.vars = uu____17467;_},uu____17468))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____17503,uu____17504) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17519;
                    FStar_Syntax_Syntax.pos = uu____17520;
                    FStar_Syntax_Syntax.vars = uu____17521;_},uu____17522),uu____17523)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17558,uu____17559) ->
                  let t21 =
                    let uu____17567 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17567  in
                  solve_t env
                    (let uu___194_17593 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___194_17593.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___194_17593.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___194_17593.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___194_17593.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___194_17593.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___194_17593.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___194_17593.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___194_17593.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___194_17593.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17594,FStar_Syntax_Syntax.Tm_refine uu____17595) ->
                  let t11 =
                    let uu____17603 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17603  in
                  solve_t env
                    (let uu___195_17629 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17629.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___195_17629.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17629.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17629.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17629.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17629.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17629.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17629.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17629.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17711 =
                    let uu____17712 = guard_of_prob env wl problem t1 t2  in
                    match uu____17712 with
                    | (guard,wl1) ->
                        let uu____17719 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17719
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____17930 = br1  in
                        (match uu____17930 with
                         | (p1,w1,uu____17955) ->
                             let uu____17972 = br2  in
                             (match uu____17972 with
                              | (p2,w2,uu____17991) ->
                                  let uu____17996 =
                                    let uu____17997 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____17997  in
                                  if uu____17996
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____18013 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____18013 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____18046 = br2  in
                                         (match uu____18046 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____18081 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____18081
                                                 in
                                              let uu____18092 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____18115,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____18132) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____18175 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____18175 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____18092
                                                (fun uu____18217  ->
                                                   match uu____18217 with
                                                   | (wprobs,wl2) ->
                                                       let uu____18238 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____18238
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____18253 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____18253
                                                              (fun
                                                                 uu____18277 
                                                                 ->
                                                                 match uu____18277
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18362 -> FStar_Pervasives_Native.None  in
                  let uu____18399 = solve_branches wl brs1 brs2  in
                  (match uu____18399 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18427 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18427 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18444 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18444  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18453 =
                              solve env
                                (attempt sub_probs1
                                   (let uu___196_18455 = wl3  in
                                    {
                                      attempting =
                                        (uu___196_18455.attempting);
                                      wl_deferred =
                                        (uu___196_18455.wl_deferred);
                                      ctr = (uu___196_18455.ctr);
                                      defer_ok = (uu___196_18455.defer_ok);
                                      smt_ok = false;
                                      tcenv = (uu___196_18455.tcenv);
                                      wl_implicits =
                                        (uu___196_18455.wl_implicits)
                                    }))
                               in
                            (match uu____18453 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____18459 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____18465,uu____18466) ->
                  let head1 =
                    let uu____18490 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18490
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18530 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18530
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18570 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18570
                    then
                      let uu____18571 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18572 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18573 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18571 uu____18572 uu____18573
                    else ());
                   (let uu____18575 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18575
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18582 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18582
                       then
                         let uu____18583 =
                           let uu____18590 =
                             let uu____18591 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18591 = FStar_Syntax_Util.Equal  in
                           if uu____18590
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18601 = mk_eq2 wl orig t1 t2  in
                              match uu____18601 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18583 with
                         | (guard,wl1) ->
                             let uu____18622 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18622
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18625,uu____18626) ->
                  let head1 =
                    let uu____18634 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18634
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18674 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18674
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18714 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18714
                    then
                      let uu____18715 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18716 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18717 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18715 uu____18716 uu____18717
                    else ());
                   (let uu____18719 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18719
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18726 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18726
                       then
                         let uu____18727 =
                           let uu____18734 =
                             let uu____18735 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18735 = FStar_Syntax_Util.Equal  in
                           if uu____18734
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18745 = mk_eq2 wl orig t1 t2  in
                              match uu____18745 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18727 with
                         | (guard,wl1) ->
                             let uu____18766 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18766
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18769,uu____18770) ->
                  let head1 =
                    let uu____18772 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18772
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18812 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18812
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18852 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18852
                    then
                      let uu____18853 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18854 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18855 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18853 uu____18854 uu____18855
                    else ());
                   (let uu____18857 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18857
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18864 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18864
                       then
                         let uu____18865 =
                           let uu____18872 =
                             let uu____18873 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18873 = FStar_Syntax_Util.Equal  in
                           if uu____18872
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18883 = mk_eq2 wl orig t1 t2  in
                              match uu____18883 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18865 with
                         | (guard,wl1) ->
                             let uu____18904 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18904
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18907,uu____18908) ->
                  let head1 =
                    let uu____18910 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18910
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18950 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18950
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18990 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18990
                    then
                      let uu____18991 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18992 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18993 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18991 uu____18992 uu____18993
                    else ());
                   (let uu____18995 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18995
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19002 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19002
                       then
                         let uu____19003 =
                           let uu____19010 =
                             let uu____19011 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19011 = FStar_Syntax_Util.Equal  in
                           if uu____19010
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19021 = mk_eq2 wl orig t1 t2  in
                              match uu____19021 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19003 with
                         | (guard,wl1) ->
                             let uu____19042 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19042
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____19045,uu____19046) ->
                  let head1 =
                    let uu____19048 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19048
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19088 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19088
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19128 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19128
                    then
                      let uu____19129 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19130 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19131 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19129 uu____19130 uu____19131
                    else ());
                   (let uu____19133 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19133
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19140 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19140
                       then
                         let uu____19141 =
                           let uu____19148 =
                             let uu____19149 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19149 = FStar_Syntax_Util.Equal  in
                           if uu____19148
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19159 = mk_eq2 wl orig t1 t2  in
                              match uu____19159 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19141 with
                         | (guard,wl1) ->
                             let uu____19180 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19180
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____19183,uu____19184) ->
                  let head1 =
                    let uu____19200 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19200
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19240 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19240
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19280 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19280
                    then
                      let uu____19281 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19282 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19283 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19281 uu____19282 uu____19283
                    else ());
                   (let uu____19285 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19285
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19292 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19292
                       then
                         let uu____19293 =
                           let uu____19300 =
                             let uu____19301 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19301 = FStar_Syntax_Util.Equal  in
                           if uu____19300
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19311 = mk_eq2 wl orig t1 t2  in
                              match uu____19311 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19293 with
                         | (guard,wl1) ->
                             let uu____19332 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19332
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19335,FStar_Syntax_Syntax.Tm_match uu____19336) ->
                  let head1 =
                    let uu____19360 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19360
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19400 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19400
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19440 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19440
                    then
                      let uu____19441 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19442 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19443 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19441 uu____19442 uu____19443
                    else ());
                   (let uu____19445 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19445
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19452 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19452
                       then
                         let uu____19453 =
                           let uu____19460 =
                             let uu____19461 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19461 = FStar_Syntax_Util.Equal  in
                           if uu____19460
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19471 = mk_eq2 wl orig t1 t2  in
                              match uu____19471 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19453 with
                         | (guard,wl1) ->
                             let uu____19492 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19492
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19495,FStar_Syntax_Syntax.Tm_uinst uu____19496) ->
                  let head1 =
                    let uu____19504 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19504
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19544 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19544
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19584 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19584
                    then
                      let uu____19585 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19586 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19587 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19585 uu____19586 uu____19587
                    else ());
                   (let uu____19589 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19589
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19596 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19596
                       then
                         let uu____19597 =
                           let uu____19604 =
                             let uu____19605 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19605 = FStar_Syntax_Util.Equal  in
                           if uu____19604
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19615 = mk_eq2 wl orig t1 t2  in
                              match uu____19615 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19597 with
                         | (guard,wl1) ->
                             let uu____19636 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19636
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19639,FStar_Syntax_Syntax.Tm_name uu____19640) ->
                  let head1 =
                    let uu____19642 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19642
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19682 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19682
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19722 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19722
                    then
                      let uu____19723 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19724 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19725 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19723 uu____19724 uu____19725
                    else ());
                   (let uu____19727 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19727
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19734 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19734
                       then
                         let uu____19735 =
                           let uu____19742 =
                             let uu____19743 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19743 = FStar_Syntax_Util.Equal  in
                           if uu____19742
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19753 = mk_eq2 wl orig t1 t2  in
                              match uu____19753 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19735 with
                         | (guard,wl1) ->
                             let uu____19774 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19774
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19777,FStar_Syntax_Syntax.Tm_constant uu____19778) ->
                  let head1 =
                    let uu____19780 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19780
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19814 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19814
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19848 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19848
                    then
                      let uu____19849 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19850 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19851 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19849 uu____19850 uu____19851
                    else ());
                   (let uu____19853 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19853
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19860 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19860
                       then
                         let uu____19861 =
                           let uu____19868 =
                             let uu____19869 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19869 = FStar_Syntax_Util.Equal  in
                           if uu____19868
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19879 = mk_eq2 wl orig t1 t2  in
                              match uu____19879 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19861 with
                         | (guard,wl1) ->
                             let uu____19900 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19900
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19903,FStar_Syntax_Syntax.Tm_fvar uu____19904) ->
                  let head1 =
                    let uu____19906 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19906
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19940 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19940
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19974 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19974
                    then
                      let uu____19975 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19976 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19977 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19975 uu____19976 uu____19977
                    else ());
                   (let uu____19979 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19979
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19986 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19986
                       then
                         let uu____19987 =
                           let uu____19994 =
                             let uu____19995 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19995 = FStar_Syntax_Util.Equal  in
                           if uu____19994
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20005 = mk_eq2 wl orig t1 t2  in
                              match uu____20005 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19987 with
                         | (guard,wl1) ->
                             let uu____20026 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20026
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____20029,FStar_Syntax_Syntax.Tm_app uu____20030) ->
                  let head1 =
                    let uu____20046 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20046
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20080 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20080
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20120 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20120
                    then
                      let uu____20121 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20122 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20123 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20121 uu____20122 uu____20123
                    else ());
                   (let uu____20125 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20125
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20132 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20132
                       then
                         let uu____20133 =
                           let uu____20140 =
                             let uu____20141 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20141 = FStar_Syntax_Util.Equal  in
                           if uu____20140
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20151 = mk_eq2 wl orig t1 t2  in
                              match uu____20151 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20133 with
                         | (guard,wl1) ->
                             let uu____20172 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20172
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____20175,FStar_Syntax_Syntax.Tm_let uu____20176) ->
                  let uu____20201 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____20201
                  then
                    let uu____20202 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____20202
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____20204,uu____20205) ->
                  let uu____20218 =
                    let uu____20223 =
                      let uu____20224 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20225 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20226 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20227 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20224 uu____20225 uu____20226 uu____20227
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20223)
                     in
                  FStar_Errors.raise_error uu____20218
                    t1.FStar_Syntax_Syntax.pos
              | (uu____20228,FStar_Syntax_Syntax.Tm_let uu____20229) ->
                  let uu____20242 =
                    let uu____20247 =
                      let uu____20248 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20249 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20250 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20251 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20248 uu____20249 uu____20250 uu____20251
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20247)
                     in
                  FStar_Errors.raise_error uu____20242
                    t1.FStar_Syntax_Syntax.pos
              | uu____20252 -> giveup env "head tag mismatch" orig))))

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
          (let uu____20311 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20311
           then
             let uu____20312 =
               let uu____20313 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____20313  in
             let uu____20314 =
               let uu____20315 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____20315  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____20312 uu____20314
           else ());
          (let uu____20317 =
             let uu____20318 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____20318  in
           if uu____20317
           then
             let uu____20319 =
               let uu____20320 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20321 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20320 uu____20321
                in
             giveup env uu____20319 orig
           else
             (let uu____20323 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____20323 with
              | (ret_sub_prob,wl1) ->
                  let uu____20330 =
                    FStar_List.fold_right2
                      (fun uu____20363  ->
                         fun uu____20364  ->
                           fun uu____20365  ->
                             match (uu____20363, uu____20364, uu____20365)
                             with
                             | ((a1,uu____20401),(a2,uu____20403),(arg_sub_probs,wl2))
                                 ->
                                 let uu____20424 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____20424 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____20330 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____20453 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____20453  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20483 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20486)::[] -> wp1
              | uu____20503 ->
                  let uu____20512 =
                    let uu____20513 =
                      let uu____20514 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20514  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20513
                     in
                  failwith uu____20512
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20520 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20520]
              | x -> x  in
            let uu____20522 =
              let uu____20531 =
                let uu____20538 =
                  let uu____20539 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20539 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20538  in
              [uu____20531]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20522;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20552 = lift_c1 ()  in solve_eq uu____20552 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___145_20558  ->
                       match uu___145_20558 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20559 -> false))
                in
             let uu____20560 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20586)::uu____20587,(wp2,uu____20589)::uu____20590)
                   -> (wp1, wp2)
               | uu____20643 ->
                   let uu____20664 =
                     let uu____20669 =
                       let uu____20670 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20671 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20670 uu____20671
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20669)
                      in
                   FStar_Errors.raise_error uu____20664
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20560 with
             | (wpc1,wpc2) ->
                 let uu____20678 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20678
                 then
                   let uu____20681 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20681 wl
                 else
                   (let uu____20683 =
                      let uu____20690 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20690  in
                    match uu____20683 with
                    | (c2_decl,qualifiers) ->
                        let uu____20711 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20711
                        then
                          let c1_repr =
                            let uu____20715 =
                              let uu____20716 =
                                let uu____20717 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20717  in
                              let uu____20718 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20716 uu____20718
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20715
                             in
                          let c2_repr =
                            let uu____20720 =
                              let uu____20721 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20722 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20721 uu____20722
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20720
                             in
                          let uu____20723 =
                            let uu____20728 =
                              let uu____20729 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20730 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20729 uu____20730
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20728
                             in
                          (match uu____20723 with
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
                                 ((let uu____20744 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20744
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20747 =
                                     let uu____20754 =
                                       let uu____20755 =
                                         let uu____20770 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20773 =
                                           let uu____20782 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20789 =
                                             let uu____20798 =
                                               let uu____20805 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20805
                                                in
                                             [uu____20798]  in
                                           uu____20782 :: uu____20789  in
                                         (uu____20770, uu____20773)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20755
                                        in
                                     FStar_Syntax_Syntax.mk uu____20754  in
                                   uu____20747 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20846 =
                                    let uu____20853 =
                                      let uu____20854 =
                                        let uu____20869 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20872 =
                                          let uu____20881 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20888 =
                                            let uu____20897 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20904 =
                                              let uu____20913 =
                                                let uu____20920 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20920
                                                 in
                                              [uu____20913]  in
                                            uu____20897 :: uu____20904  in
                                          uu____20881 :: uu____20888  in
                                        (uu____20869, uu____20872)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20854
                                       in
                                    FStar_Syntax_Syntax.mk uu____20853  in
                                  uu____20846 FStar_Pervasives_Native.None r)
                              in
                           let uu____20964 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20964 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20972 =
                                   let uu____20975 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____20975
                                    in
                                 solve_prob orig uu____20972 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____20978 = FStar_Util.physical_equality c1 c2  in
        if uu____20978
        then
          let uu____20979 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20979
        else
          ((let uu____20982 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20982
            then
              let uu____20983 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20984 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20983
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20984
            else ());
           (let uu____20986 =
              let uu____20995 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20998 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20995, uu____20998)  in
            match uu____20986 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21016),FStar_Syntax_Syntax.Total
                    (t2,uu____21018)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21035 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21035 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21036,FStar_Syntax_Syntax.Total uu____21037) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21055),FStar_Syntax_Syntax.Total
                    (t2,uu____21057)) ->
                     let uu____21074 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21074 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21076),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21078)) ->
                     let uu____21095 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21095 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21097),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21099)) ->
                     let uu____21116 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21116 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21117,FStar_Syntax_Syntax.Comp uu____21118) ->
                     let uu____21127 =
                       let uu___197_21130 = problem  in
                       let uu____21133 =
                         let uu____21134 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21134
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___197_21130.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21133;
                         FStar_TypeChecker_Common.relation =
                           (uu___197_21130.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___197_21130.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___197_21130.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___197_21130.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___197_21130.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___197_21130.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___197_21130.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___197_21130.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21127 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21135,FStar_Syntax_Syntax.Comp uu____21136) ->
                     let uu____21145 =
                       let uu___197_21148 = problem  in
                       let uu____21151 =
                         let uu____21152 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21152
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___197_21148.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21151;
                         FStar_TypeChecker_Common.relation =
                           (uu___197_21148.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___197_21148.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___197_21148.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___197_21148.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___197_21148.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___197_21148.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___197_21148.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___197_21148.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21145 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21153,FStar_Syntax_Syntax.GTotal uu____21154) ->
                     let uu____21163 =
                       let uu___198_21166 = problem  in
                       let uu____21169 =
                         let uu____21170 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21170
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___198_21166.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___198_21166.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___198_21166.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21169;
                         FStar_TypeChecker_Common.element =
                           (uu___198_21166.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___198_21166.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___198_21166.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___198_21166.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___198_21166.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___198_21166.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21163 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21171,FStar_Syntax_Syntax.Total uu____21172) ->
                     let uu____21181 =
                       let uu___198_21184 = problem  in
                       let uu____21187 =
                         let uu____21188 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21188
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___198_21184.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___198_21184.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___198_21184.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21187;
                         FStar_TypeChecker_Common.element =
                           (uu___198_21184.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___198_21184.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___198_21184.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___198_21184.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___198_21184.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___198_21184.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21181 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21189,FStar_Syntax_Syntax.Comp uu____21190) ->
                     let uu____21191 =
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
                     if uu____21191
                     then
                       let uu____21192 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21192 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21196 =
                            let uu____21201 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____21201
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21207 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21208 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21207, uu____21208))
                             in
                          match uu____21196 with
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
                           (let uu____21215 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21215
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21217 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21217 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21220 =
                                  let uu____21221 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21222 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21221 uu____21222
                                   in
                                giveup env uu____21220 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21229 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21257  ->
              match uu____21257 with
              | (uu____21266,tm,uu____21268,uu____21269) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____21229 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21302 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21302 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21320 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21348  ->
                match uu____21348 with
                | (u1,u2) ->
                    let uu____21355 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21356 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21355 uu____21356))
         in
      FStar_All.pipe_right uu____21320 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21383,[])) -> "{}"
      | uu____21408 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21431 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21431
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21434 =
              FStar_List.map
                (fun uu____21444  ->
                   match uu____21444 with
                   | (uu____21449,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21434 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21454 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21454 imps
  
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
                  let uu____21507 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21507
                  then
                    let uu____21508 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21509 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21508
                      (rel_to_string rel) uu____21509
                  else "TOP"  in
                let uu____21511 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21511 with
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
              let uu____21568 =
                let uu____21571 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21571
                 in
              FStar_Syntax_Syntax.new_bv uu____21568 t1  in
            let uu____21574 =
              let uu____21579 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21579
               in
            match uu____21574 with | (p,wl1) -> (p, x, wl1)
  
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
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21652 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21652
              then
                let uu____21653 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21653
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
          ((let uu____21675 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21675
            then
              let uu____21676 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21676
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21680 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21680
             then
               let uu____21681 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21681
             else ());
            (let f2 =
               let uu____21684 =
                 let uu____21685 = FStar_Syntax_Util.unmeta f1  in
                 uu____21685.FStar_Syntax_Syntax.n  in
               match uu____21684 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21689 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___199_21690 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___199_21690.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___199_21690.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___199_21690.FStar_TypeChecker_Env.implicits)
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
            let uu____21792 =
              let uu____21793 =
                let uu____21794 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21794;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21793  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21792
  
let with_guard_no_simp :
  'Auu____21809 .
    'Auu____21809 ->
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
            let uu____21832 =
              let uu____21833 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21833;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21832
  
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
          (let uu____21871 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21871
           then
             let uu____21872 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21873 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21872
               uu____21873
           else ());
          (let uu____21875 =
             let uu____21880 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____21880
              in
           match uu____21875 with
           | (prob,wl) ->
               let g =
                 let uu____21888 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21906  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21888  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21948 = try_teq true env t1 t2  in
        match uu____21948 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21952 = FStar_TypeChecker_Env.get_range env  in
              let uu____21953 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21952 uu____21953);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21960 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21960
              then
                let uu____21961 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21962 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21963 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21961
                  uu____21962 uu____21963
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
          let uu____21985 = FStar_TypeChecker_Env.get_range env  in
          let uu____21986 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21985 uu____21986
  
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
        (let uu____22011 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22011
         then
           let uu____22012 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22013 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____22012 uu____22013
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____22016 =
           let uu____22023 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____22023 "sub_comp"
            in
         match uu____22016 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____22033 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____22051  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____22033)
  
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
      fun uu____22104  ->
        match uu____22104 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22147 =
                 let uu____22152 =
                   let uu____22153 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22154 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22153 uu____22154
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22152)  in
               let uu____22155 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22147 uu____22155)
               in
            let equiv1 v1 v' =
              let uu____22167 =
                let uu____22172 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22173 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22172, uu____22173)  in
              match uu____22167 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22192 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22222 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22222 with
                      | FStar_Syntax_Syntax.U_unif uu____22229 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22258  ->
                                    match uu____22258 with
                                    | (u,v') ->
                                        let uu____22267 = equiv1 v1 v'  in
                                        if uu____22267
                                        then
                                          let uu____22270 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22270 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22286 -> []))
               in
            let uu____22291 =
              let wl =
                let uu___200_22295 = empty_worklist env  in
                {
                  attempting = (uu___200_22295.attempting);
                  wl_deferred = (uu___200_22295.wl_deferred);
                  ctr = (uu___200_22295.ctr);
                  defer_ok = false;
                  smt_ok = (uu___200_22295.smt_ok);
                  tcenv = (uu___200_22295.tcenv);
                  wl_implicits = (uu___200_22295.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22313  ->
                      match uu____22313 with
                      | (lb,v1) ->
                          let uu____22320 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22320 with
                           | USolved wl1 -> ()
                           | uu____22322 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22332 =
              match uu____22332 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22341) -> true
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
                      uu____22364,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22366,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22377) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22384,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22392 -> false)
               in
            let uu____22397 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22412  ->
                      match uu____22412 with
                      | (u,v1) ->
                          let uu____22419 = check_ineq (u, v1)  in
                          if uu____22419
                          then true
                          else
                            ((let uu____22422 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22422
                              then
                                let uu____22423 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22424 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22423
                                  uu____22424
                              else ());
                             false)))
               in
            if uu____22397
            then ()
            else
              ((let uu____22428 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22428
                then
                  ((let uu____22430 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22430);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22440 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22440))
                else ());
               (let uu____22450 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22450))
  
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
        let fail1 uu____22517 =
          match uu____22517 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___201_22538 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___201_22538.attempting);
            wl_deferred = (uu___201_22538.wl_deferred);
            ctr = (uu___201_22538.ctr);
            defer_ok;
            smt_ok = (uu___201_22538.smt_ok);
            tcenv = (uu___201_22538.tcenv);
            wl_implicits = (uu___201_22538.wl_implicits)
          }  in
        (let uu____22540 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22540
         then
           let uu____22541 = FStar_Util.string_of_bool defer_ok  in
           let uu____22542 = wl_to_string wl  in
           let uu____22543 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22541 uu____22542 uu____22543
         else ());
        (let g1 =
           let uu____22554 = solve_and_commit env wl fail1  in
           match uu____22554 with
           | FStar_Pervasives_Native.Some
               (uu____22561::uu____22562,uu____22563) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___202_22588 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___202_22588.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___202_22588.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22597 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___203_22605 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___203_22605.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___203_22605.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___203_22605.FStar_TypeChecker_Env.implicits)
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
    let uu____22653 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22653 with
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
            let uu___204_22776 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___204_22776.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___204_22776.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___204_22776.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22777 =
            let uu____22778 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22778  in
          if uu____22777
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22786 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22787 =
                       let uu____22788 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22788
                        in
                     FStar_Errors.diag uu____22786 uu____22787)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22792 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22793 =
                        let uu____22794 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22794
                         in
                      FStar_Errors.diag uu____22792 uu____22793)
                   else ();
                   (let uu____22797 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22797 "discharge_guard'"
                      env vc1);
                   (let uu____22798 = check_trivial vc1  in
                    match uu____22798 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22805 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22806 =
                                let uu____22807 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22807
                                 in
                              FStar_Errors.diag uu____22805 uu____22806)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22812 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22813 =
                                let uu____22814 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22814
                                 in
                              FStar_Errors.diag uu____22812 uu____22813)
                           else ();
                           (let vcs =
                              let uu____22827 = FStar_Options.use_tactics ()
                                 in
                              if uu____22827
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22849  ->
                                     (let uu____22851 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22851);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22894  ->
                                              match uu____22894 with
                                              | (env1,goal,opts) ->
                                                  let uu____22910 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22910, opts)))))
                              else
                                (let uu____22912 =
                                   let uu____22921 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22921)  in
                                 [uu____22912])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22964  ->
                                    match uu____22964 with
                                    | (env1,goal,opts) ->
                                        let uu____22980 = check_trivial goal
                                           in
                                        (match uu____22980 with
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
                                                (let uu____22988 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22989 =
                                                   let uu____22990 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22991 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22990 uu____22991
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22988 uu____22989)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22994 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22995 =
                                                   let uu____22996 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22996
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22994 uu____22995)
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
      let uu____23010 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23010 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23017 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23017
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23028 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23028 with
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
            let uu____23061 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____23061 with
            | FStar_Pervasives_Native.Some uu____23064 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____23084 = acc  in
            match uu____23084 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____23136 = hd1  in
                     (match uu____23136 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23150 = unresolved ctx_u  in
                             if uu____23150
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___205_23162 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___205_23162.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___205_23162.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___205_23162.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___205_23162.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___205_23162.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___205_23162.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___205_23162.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___205_23162.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___205_23162.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___205_23162.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___205_23162.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___205_23162.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___205_23162.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___205_23162.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___205_23162.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___205_23162.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___205_23162.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___205_23162.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___205_23162.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___205_23162.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___205_23162.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___205_23162.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___205_23162.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___205_23162.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___205_23162.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___205_23162.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___205_23162.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___205_23162.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___205_23162.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___205_23162.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___205_23162.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___205_23162.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___205_23162.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___205_23162.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___205_23162.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___205_23162.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___205_23162.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___205_23162.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___206_23165 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___206_23165.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___206_23165.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___206_23165.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___206_23165.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___206_23165.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___206_23165.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___206_23165.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___206_23165.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___206_23165.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___206_23165.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___206_23165.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___206_23165.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___206_23165.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___206_23165.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___206_23165.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___206_23165.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___206_23165.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___206_23165.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___206_23165.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___206_23165.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___206_23165.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___206_23165.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___206_23165.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___206_23165.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___206_23165.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___206_23165.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___206_23165.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___206_23165.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___206_23165.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___206_23165.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___206_23165.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___206_23165.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___206_23165.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___206_23165.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___206_23165.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___206_23165.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___206_23165.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___206_23165.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____23168 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23168
                                   then
                                     let uu____23169 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____23170 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____23171 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____23172 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____23169 uu____23170 uu____23171
                                       reason uu____23172
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____23183 =
                                             let uu____23192 =
                                               let uu____23199 =
                                                 let uu____23200 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____23201 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____23202 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____23200 uu____23201
                                                   uu____23202
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____23199, r)
                                                in
                                             [uu____23192]  in
                                           FStar_Errors.add_errors
                                             uu____23183);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___209_23216 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___209_23216.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___209_23216.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___209_23216.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____23219 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____23229  ->
                                               let uu____23230 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____23231 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____23232 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____23230 uu____23231
                                                 reason uu____23232)) env2 g2
                                         true
                                        in
                                     match uu____23219 with
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
          let uu___210_23242 = g  in
          let uu____23243 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___210_23242.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___210_23242.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___210_23242.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23243
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
        let uu____23293 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23293 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23302 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23302
      | (reason,e,ctx_u,r)::uu____23307 ->
          let uu____23326 =
            let uu____23331 =
              let uu____23332 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23333 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23332 uu____23333 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23331)
             in
          FStar_Errors.raise_error uu____23326 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___211_23344 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___211_23344.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___211_23344.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___211_23344.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23359 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23359 with
      | FStar_Pervasives_Native.Some uu____23365 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23381 = try_teq false env t1 t2  in
        match uu____23381 with
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
        (let uu____23415 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23415
         then
           let uu____23416 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23417 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23416
             uu____23417
         else ());
        (let uu____23419 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23419 with
         | (prob,x,wl) ->
             let g =
               let uu____23438 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23456  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23438  in
             ((let uu____23484 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23484
               then
                 let uu____23485 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23486 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23487 =
                   let uu____23488 = FStar_Util.must g  in
                   guard_to_string env uu____23488  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23485 uu____23486 uu____23487
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
        let uu____23522 = check_subtyping env t1 t2  in
        match uu____23522 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23541 =
              let uu____23542 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23542 g  in
            FStar_Pervasives_Native.Some uu____23541
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23560 = check_subtyping env t1 t2  in
        match uu____23560 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23579 =
              let uu____23580 =
                let uu____23581 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23581]  in
              close_guard env uu____23580 g  in
            FStar_Pervasives_Native.Some uu____23579
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23610 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23610
         then
           let uu____23611 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23612 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23611
             uu____23612
         else ());
        (let uu____23614 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23614 with
         | (prob,x,wl) ->
             let g =
               let uu____23627 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23645  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23627  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23674 =
                      let uu____23675 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23675]  in
                    close_guard env uu____23674 g1  in
                  discharge_guard_nosmt env g2))
  