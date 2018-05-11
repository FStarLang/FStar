open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____11 =
      let uu____12 = FStar_Syntax_Util.unmeta t  in
      uu____12.FStar_Syntax_Syntax.n  in
    match uu____11 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____16 -> false
  
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
             (fun uu____90  ->
                match uu____90 with
                | (uu____99,uu____100,ctx_uvar,uu____102) ->
                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_should_check =
                       FStar_Syntax_Syntax.Allow_unresolved)
                      ||
                      (let uu____105 =
                         FStar_Syntax_Unionfind.find
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       (match uu____105 with
                        | FStar_Pervasives_Native.Some uu____108 -> true
                        | FStar_Pervasives_Native.None  -> false))))
    | uu____109 -> false
  
let (is_trivial_guard_formula : FStar_TypeChecker_Env.guard_t -> Prims.bool)
  =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = uu____115;
        FStar_TypeChecker_Env.univ_ineqs = uu____116;
        FStar_TypeChecker_Env.implicits = uu____117;_} -> true
    | uu____136 -> false
  
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
          let uu___146_171 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___146_171.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___146_171.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___146_171.FStar_TypeChecker_Env.implicits)
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
          let uu____206 = FStar_Options.defensive ()  in
          if uu____206
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____210 =
              let uu____211 =
                let uu____212 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____212  in
              Prims.op_Negation uu____211  in
            (if uu____210
             then
               let uu____217 =
                 let uu____222 =
                   let uu____223 = FStar_Syntax_Print.term_to_string t  in
                   let uu____224 =
                     let uu____225 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____225
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____223 uu____224
                    in
                 (FStar_Errors.Warning_Defensive, uu____222)  in
               FStar_Errors.log_issue rng uu____217
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> unit) =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____247 =
          let uu____248 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____248  in
        if uu____247
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
          let uu____274 =
            let uu____275 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____275  in
          if uu____274
          then ()
          else
            (let uu____277 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____277 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____300 =
            let uu____301 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____301  in
          if uu____300
          then ()
          else
            (let uu____303 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____303 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___147_317 = g  in
          let uu____318 =
            let uu____319 =
              let uu____320 =
                let uu____327 =
                  let uu____328 =
                    let uu____343 =
                      let uu____352 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____352]  in
                    (f, uu____343)  in
                  FStar_Syntax_Syntax.Tm_app uu____328  in
                FStar_Syntax_Syntax.mk uu____327  in
              uu____320 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
              uu____319
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____318;
            FStar_TypeChecker_Env.deferred =
              (uu___147_317.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___147_317.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___147_317.FStar_TypeChecker_Env.implicits)
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
          let uu___148_400 = g  in
          let uu____401 =
            let uu____402 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____402  in
          {
            FStar_TypeChecker_Env.guard_f = uu____401;
            FStar_TypeChecker_Env.deferred =
              (uu___148_400.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___148_400.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___148_400.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____408 -> failwith "impossible"
  
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
          let uu____423 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____423
  
let (check_trivial :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Common.guard_formula)
  =
  fun t  ->
    let uu____433 =
      let uu____434 = FStar_Syntax_Util.unmeta t  in
      uu____434.FStar_Syntax_Syntax.n  in
    match uu____433 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____438 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____479 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____479;
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
                       let uu____564 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____564
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___149_566 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___149_566.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___149_566.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___149_566.FStar_TypeChecker_Env.implicits)
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
               let uu____607 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____607
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
            let uu___150_626 = g  in
            let uu____627 =
              let uu____628 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____628  in
            {
              FStar_TypeChecker_Env.guard_f = uu____627;
              FStar_TypeChecker_Env.deferred =
                (uu___150_626.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___150_626.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___150_626.FStar_TypeChecker_Env.implicits)
            }
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____657 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____687 -> false
  
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
                  let uu____974 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____974;
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
                   (let uu___151_1008 = wl  in
                    {
                      attempting = (uu___151_1008.attempting);
                      wl_deferred = (uu___151_1008.wl_deferred);
                      ctr = (uu___151_1008.ctr);
                      defer_ok = (uu___151_1008.defer_ok);
                      smt_ok = (uu___151_1008.smt_ok);
                      tcenv = (uu___151_1008.tcenv);
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
    match projectee with | Success _0 -> true | uu____1070 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1100 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____1125 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1131 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1137 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___114_1152  ->
    match uu___114_1152 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1158 = FStar_Syntax_Util.head_and_args t  in
    match uu____1158 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1217 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1218 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1232 =
                     let uu____1233 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1233  in
                   FStar_Util.format1 "@<%s>" uu____1232
                in
             let uu____1236 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1217 uu____1218 uu____1236
         | uu____1237 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___115_1247  ->
      match uu___115_1247 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1251 =
            let uu____1254 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1255 =
              let uu____1258 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1259 =
                let uu____1262 =
                  let uu____1265 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1265]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1262
                 in
              uu____1258 :: uu____1259  in
            uu____1254 :: uu____1255  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1251
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1269 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1270 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1271 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1269 uu____1270
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1271
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___116_1281  ->
      match uu___116_1281 with
      | UNIV (u,t) ->
          let x =
            let uu____1285 = FStar_Options.hide_uvar_nums ()  in
            if uu____1285
            then "?"
            else
              (let uu____1287 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1287 FStar_Util.string_of_int)
             in
          let uu____1288 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1288
      | TERM (u,t) ->
          let x =
            let uu____1292 = FStar_Options.hide_uvar_nums ()  in
            if uu____1292
            then "?"
            else
              (let uu____1294 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1294 FStar_Util.string_of_int)
             in
          let uu____1295 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1295
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1310 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1310 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1324 =
      let uu____1327 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1327
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1324 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1340 .
    (FStar_Syntax_Syntax.term,'Auu____1340) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1358 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1376  ->
              match uu____1376 with
              | (x,uu____1382) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1358 (FStar_String.concat " ")
  
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
        let uu___152_1419 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___152_1419.wl_deferred);
          ctr = (uu___152_1419.ctr);
          defer_ok = (uu___152_1419.defer_ok);
          smt_ok;
          tcenv = (uu___152_1419.tcenv);
          wl_implicits = (uu___152_1419.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1426 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1426,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___153_1449 = empty_worklist env  in
      let uu____1450 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1450;
        wl_deferred = (uu___153_1449.wl_deferred);
        ctr = (uu___153_1449.ctr);
        defer_ok = (uu___153_1449.defer_ok);
        smt_ok = (uu___153_1449.smt_ok);
        tcenv = (uu___153_1449.tcenv);
        wl_implicits = (uu___153_1449.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___154_1470 = wl  in
        {
          attempting = (uu___154_1470.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___154_1470.ctr);
          defer_ok = (uu___154_1470.defer_ok);
          smt_ok = (uu___154_1470.smt_ok);
          tcenv = (uu___154_1470.tcenv);
          wl_implicits = (uu___154_1470.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___155_1491 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___155_1491.wl_deferred);
        ctr = (uu___155_1491.ctr);
        defer_ok = (uu___155_1491.defer_ok);
        smt_ok = (uu___155_1491.smt_ok);
        tcenv = (uu___155_1491.tcenv);
        wl_implicits = (uu___155_1491.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1508 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1508
         then
           let uu____1509 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1509
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___117_1515  ->
    match uu___117_1515 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1520 .
    'Auu____1520 FStar_TypeChecker_Common.problem ->
      'Auu____1520 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___156_1532 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___156_1532.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___156_1532.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___156_1532.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___156_1532.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___156_1532.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___156_1532.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___156_1532.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1539 .
    'Auu____1539 FStar_TypeChecker_Common.problem ->
      'Auu____1539 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___118_1556  ->
    match uu___118_1556 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.TProb _0_17)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.CProb _0_18)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___119_1571  ->
    match uu___119_1571 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___157_1577 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___157_1577.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___157_1577.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___157_1577.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___157_1577.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___157_1577.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___157_1577.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___157_1577.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___157_1577.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___157_1577.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___158_1585 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___158_1585.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___158_1585.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___158_1585.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___158_1585.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___158_1585.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___158_1585.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___158_1585.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___158_1585.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___158_1585.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___120_1597  ->
      match uu___120_1597 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___121_1602  ->
    match uu___121_1602 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___122_1613  ->
    match uu___122_1613 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___123_1626  ->
    match uu___123_1626 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___124_1639  ->
    match uu___124_1639 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___125_1650  ->
    match uu___125_1650 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___126_1665  ->
    match uu___126_1665 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1684 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1684) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1712 =
          let uu____1713 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1713  in
        if uu____1712
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1747)::bs ->
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
        let uu____1814 =
          let uu____1815 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1815  in
        if uu____1814
        then ()
        else
          (let uu____1817 =
             let uu____1820 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1820
              in
           def_check_closed_in (p_loc prob) msg uu____1817 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1850 =
         let uu____1851 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1851  in
       if uu____1850
       then ()
       else
         (let uu____1853 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1853));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1865 -> ())
  
let mk_eq2 :
  'Auu____1877 .
    worklist ->
      'Auu____1877 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1906 = FStar_Syntax_Util.type_u ()  in
          match uu____1906 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1918 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1918 with
               | (uu____1929,tt,wl1) ->
                   let uu____1932 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1932, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___127_1937  ->
    match uu___127_1937 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1953 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1953 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1963  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2061 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2061 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2061 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2061 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2127 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2127  in
                  let uu____2130 =
                    let uu____2137 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2137
                      guard_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2130 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2158 ->
                            let uu____2165 =
                              let uu____2170 =
                                FStar_List.map
                                  (fun uu____2183  ->
                                     match uu____2183 with
                                     | (x,i) ->
                                         let uu____2194 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2194, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2170  in
                            uu____2165 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2197 =
                        let uu____2200 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2200;
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
                      (uu____2197, wl1)
  
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
                  let uu____2263 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2263 with
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
                  let uu____2340 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2340 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2375 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2375 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2375 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2375 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2426 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2463 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2463]  in
                        let uu____2476 =
                          let uu____2479 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2479  in
                        let uu____2482 =
                          let uu____2485 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2485  in
                        (bs, uu____2476, uu____2482)
                     in
                  match uu____2426 with
                  | (bs,lg_ty,elt) ->
                      let uu____2507 =
                        let uu____2514 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___159_2522 = wl  in
                           {
                             attempting = (uu___159_2522.attempting);
                             wl_deferred = (uu___159_2522.wl_deferred);
                             ctr = (uu___159_2522.ctr);
                             defer_ok = (uu___159_2522.defer_ok);
                             smt_ok = (uu___159_2522.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___159_2522.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2514
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2507 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2534 =
                                   let uu____2539 =
                                     let uu____2540 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2540]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2539
                                    in
                                 uu____2534 FStar_Pervasives_Native.None loc
                              in
                           let uu____2561 =
                             let uu____2564 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2564;
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
                           (uu____2561, wl1))
  
let problem_using_guard :
  'Auu____2581 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2581 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2581 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2581 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2618 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2618;
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
  'Auu____2629 .
    worklist ->
      'Auu____2629 FStar_TypeChecker_Common.problem ->
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
        let uu____2679 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2679
        then
          let uu____2680 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2681 = prob_to_string env d  in
          let uu____2682 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2680 uu____2681 uu____2682 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2688 -> failwith "impossible"  in
           let uu____2689 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2701 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2702 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2701, uu____2702)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2706 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2707 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2706, uu____2707)
              in
           match uu____2689 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___128_2725  ->
            match uu___128_2725 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2737 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___129_2759  ->
           match uu___129_2759 with
           | UNIV uu____2762 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2769 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2769
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
        (fun uu___130_2793  ->
           match uu___130_2793 with
           | UNIV (u',t) ->
               let uu____2798 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2798
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2802 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2813 =
        let uu____2814 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2814
         in
      FStar_Syntax_Subst.compress uu____2813
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2825 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2825
  
let norm_arg :
  'Auu____2832 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2832) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2832)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2855 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2855, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2896  ->
              match uu____2896 with
              | (x,imp) ->
                  let uu____2907 =
                    let uu___160_2908 = x  in
                    let uu____2909 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___160_2908.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___160_2908.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2909
                    }  in
                  (uu____2907, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2930 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2930
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2934 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2934
        | uu____2937 -> u2  in
      let uu____2938 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2938
  
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
                (let uu____3060 = norm_refinement env t12  in
                 match uu____3060 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3077;
                     FStar_Syntax_Syntax.vars = uu____3078;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3104 =
                       let uu____3105 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3106 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3105 uu____3106
                        in
                     failwith uu____3104)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3122 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3122
          | FStar_Syntax_Syntax.Tm_uinst uu____3123 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3162 =
                   let uu____3163 = FStar_Syntax_Subst.compress t1'  in
                   uu____3163.FStar_Syntax_Syntax.n  in
                 match uu____3162 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3180 -> aux true t1'
                 | uu____3187 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3204 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3237 =
                   let uu____3238 = FStar_Syntax_Subst.compress t1'  in
                   uu____3238.FStar_Syntax_Syntax.n  in
                 match uu____3237 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3255 -> aux true t1'
                 | uu____3262 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3279 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3326 =
                   let uu____3327 = FStar_Syntax_Subst.compress t1'  in
                   uu____3327.FStar_Syntax_Syntax.n  in
                 match uu____3326 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3344 -> aux true t1'
                 | uu____3351 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3368 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3385 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3402 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3419 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3436 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3465 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3498 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3521 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3552 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3581 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3620 ->
              let uu____3627 =
                let uu____3628 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3629 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3628 uu____3629
                 in
              failwith uu____3627
          | FStar_Syntax_Syntax.Tm_ascribed uu____3644 ->
              let uu____3671 =
                let uu____3672 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3673 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3672 uu____3673
                 in
              failwith uu____3671
          | FStar_Syntax_Syntax.Tm_delayed uu____3688 ->
              let uu____3713 =
                let uu____3714 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3715 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3714 uu____3715
                 in
              failwith uu____3713
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3730 =
                let uu____3731 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3732 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3731 uu____3732
                 in
              failwith uu____3730
           in
        let uu____3747 = whnf env t1  in aux false uu____3747
  
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
      let uu____3793 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3793 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3829 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3829, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3840 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3840 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3867 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3867 with
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
  fun uu____3954  ->
    match uu____3954 with
    | (t_base,refopt) ->
        let uu____3987 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3987 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4027 =
      let uu____4030 =
        let uu____4033 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4056  ->
                  match uu____4056 with | (uu____4063,uu____4064,x) -> x))
           in
        FStar_List.append wl.attempting uu____4033  in
      FStar_List.map (wl_prob_to_string wl) uu____4030  in
    FStar_All.pipe_right uu____4027 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4078 .
    ('Auu____4078,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4089  ->
    match uu____4089 with
    | (uu____4096,c,args) ->
        let uu____4099 = print_ctx_uvar c  in
        let uu____4100 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4099 uu____4100
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4106 = FStar_Syntax_Util.head_and_args t  in
    match uu____4106 with
    | (head1,_args) ->
        let uu____4143 =
          let uu____4144 = FStar_Syntax_Subst.compress head1  in
          uu____4144.FStar_Syntax_Syntax.n  in
        (match uu____4143 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4147 -> true
         | uu____4162 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4168 = FStar_Syntax_Util.head_and_args t  in
    match uu____4168 with
    | (head1,_args) ->
        let uu____4205 =
          let uu____4206 = FStar_Syntax_Subst.compress head1  in
          uu____4206.FStar_Syntax_Syntax.n  in
        (match uu____4205 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4210) -> u
         | uu____4231 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4254 = FStar_Syntax_Util.head_and_args t  in
      match uu____4254 with
      | (head1,args) ->
          let uu____4295 =
            let uu____4296 = FStar_Syntax_Subst.compress head1  in
            uu____4296.FStar_Syntax_Syntax.n  in
          (match uu____4295 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4304)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4347 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___131_4372  ->
                         match uu___131_4372 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4376 =
                               let uu____4377 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4377.FStar_Syntax_Syntax.n  in
                             (match uu____4376 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4381 -> false)
                         | uu____4382 -> true))
                  in
               (match uu____4347 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4404 =
                        FStar_List.collect
                          (fun uu___132_4414  ->
                             match uu___132_4414 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4418 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4418]
                             | uu____4419 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4404 FStar_List.rev  in
                    let uu____4436 =
                      let uu____4443 =
                        let uu____4450 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___133_4468  ->
                                  match uu___133_4468 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4472 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4472]
                                  | uu____4473 -> []))
                           in
                        FStar_All.pipe_right uu____4450 FStar_List.rev  in
                      let uu____4490 =
                        let uu____4493 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4493  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4443 uu____4490
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4436 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4522  ->
                                match uu____4522 with
                                | (x,i) ->
                                    let uu____4533 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4533, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4556  ->
                                match uu____4556 with
                                | (a,i) ->
                                    let uu____4567 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4567, i)) args_sol
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
           | uu____4583 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4603 =
          let uu____4624 =
            let uu____4625 = FStar_Syntax_Subst.compress k  in
            uu____4625.FStar_Syntax_Syntax.n  in
          match uu____4624 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4694 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4694)
              else
                (let uu____4724 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4724 with
                 | (ys',t1,uu____4755) ->
                     let uu____4760 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4760))
          | uu____4793 ->
              let uu____4794 =
                let uu____4799 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4799)  in
              ((ys, t), uu____4794)
           in
        match uu____4603 with
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
                 let uu____4876 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4876 c  in
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
               (let uu____4950 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4950
                then
                  let uu____4951 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4952 = print_ctx_uvar uv  in
                  let uu____4953 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4951 uu____4952 uu____4953
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
             let uu____4959 = p_guard_uvar prob  in
             match uu____4959 with
             | (xs,uv) ->
                 let fail1 uu____4971 =
                   let uu____4972 =
                     let uu____4973 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4974 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4973 uu____4974
                      in
                   failwith uu____4972  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____5024  ->
                           match uu____5024 with
                           | (a,i) ->
                               let uu____5037 =
                                 let uu____5038 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____5038.FStar_Syntax_Syntax.n  in
                               (match uu____5037 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____5056 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____5064 =
                     let uu____5065 = is_flex g  in
                     Prims.op_Negation uu____5065  in
                   if uu____5064
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____5069 = destruct_flex_t g wl  in
                      match uu____5069 with
                      | ((uu____5074,uv1,args),wl1) ->
                          ((let uu____5079 = args_as_binders args  in
                            assign_solution uu____5079 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___161_5081 = wl1  in
                   {
                     attempting = (uu___161_5081.attempting);
                     wl_deferred = (uu___161_5081.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___161_5081.defer_ok);
                     smt_ok = (uu___161_5081.smt_ok);
                     tcenv = (uu___161_5081.tcenv);
                     wl_implicits = (uu___161_5081.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5102 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5102
         then
           let uu____5103 = FStar_Util.string_of_int pid  in
           let uu____5104 =
             let uu____5105 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5105 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5103 uu____5104
         else ());
        commit sol;
        (let uu___162_5112 = wl  in
         {
           attempting = (uu___162_5112.attempting);
           wl_deferred = (uu___162_5112.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___162_5112.defer_ok);
           smt_ok = (uu___162_5112.smt_ok);
           tcenv = (uu___162_5112.tcenv);
           wl_implicits = (uu___162_5112.wl_implicits)
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
             | (uu____5174,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5202 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5202
              in
           (let uu____5208 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5208
            then
              let uu____5209 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5210 =
                let uu____5211 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5211 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5209 uu____5210
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
        let uu____5236 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5236 FStar_Util.set_elements  in
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
      let uu____5270 = occurs uk t  in
      match uu____5270 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5299 =
                 let uu____5300 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5301 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5300 uu____5301
                  in
               FStar_Pervasives_Native.Some uu____5299)
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
            let uu____5390 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5390 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5434 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5482  ->
             match uu____5482 with
             | (x,uu____5492) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5505 = FStar_List.last bs  in
      match uu____5505 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5523) ->
          let uu____5528 =
            FStar_Util.prefix_until
              (fun uu___134_5543  ->
                 match uu___134_5543 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5545 -> false) g
             in
          (match uu____5528 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5558,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5594 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5594 with
        | (pfx,uu____5604) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5616 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5616 with
             | (uu____5623,src',wl1) ->
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
                 | uu____5723 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5724 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5778  ->
                  fun uu____5779  ->
                    match (uu____5778, uu____5779) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5860 =
                          let uu____5861 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5861
                           in
                        if uu____5860
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5886 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5886
                           then
                             let uu____5899 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5899)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5724 with | (isect,uu____5936) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5965 'Auu____5966 .
    (FStar_Syntax_Syntax.bv,'Auu____5965) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5966) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6023  ->
              fun uu____6024  ->
                match (uu____6023, uu____6024) with
                | ((a,uu____6042),(b,uu____6044)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6059 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6059) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6089  ->
           match uu____6089 with
           | (y,uu____6095) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6104 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6104) FStar_Pervasives_Native.tuple2
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
                   let uu____6234 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6234
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6254 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6297 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6335 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6348 -> false
  
let string_of_option :
  'Auu____6355 .
    ('Auu____6355 -> Prims.string) ->
      'Auu____6355 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___135_6370  ->
      match uu___135_6370 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6376 = f x  in Prims.strcat "Some " uu____6376
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___136_6381  ->
    match uu___136_6381 with
    | MisMatch (d1,d2) ->
        let uu____6392 =
          let uu____6393 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6394 =
            let uu____6395 =
              let uu____6396 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6396 ")"  in
            Prims.strcat ") (" uu____6395  in
          Prims.strcat uu____6393 uu____6394  in
        Prims.strcat "MisMatch (" uu____6392
    | HeadMatch u ->
        let uu____6398 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6398
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___137_6403  ->
    match uu___137_6403 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6418 -> HeadMatch false
  
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
          let uu____6432 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6432 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6443 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6466 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6475 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6503 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6503
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6504 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6505 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6506 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6521 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6534 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6558) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6564,uu____6565) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6607) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6628;
             FStar_Syntax_Syntax.index = uu____6629;
             FStar_Syntax_Syntax.sort = t2;_},uu____6631)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6638 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6639 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6640 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6653 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6660 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6678 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6678
  
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
            let uu____6705 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6705
            then FullMatch
            else
              (let uu____6707 =
                 let uu____6716 =
                   let uu____6719 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6719  in
                 let uu____6720 =
                   let uu____6723 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6723  in
                 (uu____6716, uu____6720)  in
               MisMatch uu____6707)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6729),FStar_Syntax_Syntax.Tm_uinst (g,uu____6731)) ->
            let uu____6740 = head_matches env f g  in
            FStar_All.pipe_right uu____6740 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6743 = FStar_Const.eq_const c d  in
            if uu____6743
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6750),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6752)) ->
            let uu____6793 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6793
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6800),FStar_Syntax_Syntax.Tm_refine (y,uu____6802)) ->
            let uu____6811 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6811 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6813),uu____6814) ->
            let uu____6819 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6819 head_match
        | (uu____6820,FStar_Syntax_Syntax.Tm_refine (x,uu____6822)) ->
            let uu____6827 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6827 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6828,FStar_Syntax_Syntax.Tm_type
           uu____6829) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6830,FStar_Syntax_Syntax.Tm_arrow uu____6831) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6857),FStar_Syntax_Syntax.Tm_app (head',uu____6859))
            ->
            let uu____6900 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6900 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6902),uu____6903) ->
            let uu____6924 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6924 head_match
        | (uu____6925,FStar_Syntax_Syntax.Tm_app (head1,uu____6927)) ->
            let uu____6948 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6948 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6949,FStar_Syntax_Syntax.Tm_let
           uu____6950) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6975,FStar_Syntax_Syntax.Tm_match uu____6976) ->
            HeadMatch true
        | uu____7021 ->
            let uu____7026 =
              let uu____7035 = delta_depth_of_term env t11  in
              let uu____7038 = delta_depth_of_term env t21  in
              (uu____7035, uu____7038)  in
            MisMatch uu____7026
  
let head_matches_delta :
  'Auu____7055 .
    FStar_TypeChecker_Env.env ->
      'Auu____7055 ->
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
            (let uu____7104 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7104
             then
               let uu____7105 = FStar_Syntax_Print.term_to_string t  in
               let uu____7106 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7105 uu____7106
             else ());
            (let uu____7108 =
               let uu____7109 = FStar_Syntax_Util.un_uinst head1  in
               uu____7109.FStar_Syntax_Syntax.n  in
             match uu____7108 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7115 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7115 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7129 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7129
                        then
                          let uu____7130 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7130
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7132 ->
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
                      ((let uu____7143 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7143
                        then
                          let uu____7144 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7145 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7144
                            uu____7145
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7147 -> FStar_Pervasives_Native.None)
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
            (let uu____7285 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7285
             then
               let uu____7286 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7287 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7288 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7286
                 uu____7287 uu____7288
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7312 =
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
               match uu____7312 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7357 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7357 with
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
                  uu____7389),uu____7390)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7408 =
                      let uu____7417 = maybe_inline t11  in
                      let uu____7420 = maybe_inline t21  in
                      (uu____7417, uu____7420)  in
                    match uu____7408 with
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
                 (uu____7457,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7458))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7476 =
                      let uu____7485 = maybe_inline t11  in
                      let uu____7488 = maybe_inline t21  in
                      (uu____7485, uu____7488)  in
                    match uu____7476 with
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
             | MisMatch uu____7537 -> fail1 n_delta r t11 t21
             | uu____7546 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7559 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7559
           then
             let uu____7560 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7561 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7562 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7569 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7587 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7587
                    (fun uu____7621  ->
                       match uu____7621 with
                       | (t11,t21) ->
                           let uu____7628 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7629 =
                             let uu____7630 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7630  in
                           Prims.strcat uu____7628 uu____7629))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7560 uu____7561 uu____7562 uu____7569
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7642 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7642 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___138_7655  ->
    match uu___138_7655 with
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
      let uu___163_7692 = p  in
      let uu____7695 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7696 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___163_7692.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7695;
        FStar_TypeChecker_Common.relation =
          (uu___163_7692.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7696;
        FStar_TypeChecker_Common.element =
          (uu___163_7692.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___163_7692.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___163_7692.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___163_7692.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___163_7692.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___163_7692.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7710 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7710
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7715 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7737 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7737 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7745 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7745 with
           | (lh,lhs_args) ->
               let uu____7786 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7786 with
                | (rh,rhs_args) ->
                    let uu____7827 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7840,FStar_Syntax_Syntax.Tm_uvar uu____7841)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7922 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7945,uu____7946)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7963,FStar_Syntax_Syntax.Tm_uvar uu____7964)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7981,FStar_Syntax_Syntax.Tm_arrow uu____7982)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_8012 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_8012.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_8012.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_8012.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_8012.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_8012.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_8012.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_8012.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_8012.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_8012.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8015,FStar_Syntax_Syntax.Tm_type uu____8016)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_8034 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_8034.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_8034.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_8034.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_8034.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_8034.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_8034.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_8034.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_8034.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_8034.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8037,FStar_Syntax_Syntax.Tm_uvar uu____8038)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_8056 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_8056.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_8056.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_8056.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_8056.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_8056.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_8056.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_8056.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_8056.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_8056.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8059,FStar_Syntax_Syntax.Tm_uvar uu____8060)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8077,uu____8078)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8095,FStar_Syntax_Syntax.Tm_uvar uu____8096)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8113,uu____8114) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7827 with
                     | (rank,tp1) ->
                         let uu____8127 =
                           FStar_All.pipe_right
                             (let uu___165_8131 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___165_8131.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___165_8131.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___165_8131.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___165_8131.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___165_8131.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___165_8131.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___165_8131.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___165_8131.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___165_8131.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8127))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8137 =
            FStar_All.pipe_right
              (let uu___166_8141 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___166_8141.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___166_8141.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___166_8141.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___166_8141.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___166_8141.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___166_8141.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___166_8141.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___166_8141.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___166_8141.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8137)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8202 probs =
      match uu____8202 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8283 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8304 = rank wl.tcenv hd1  in
               (match uu____8304 with
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
                      (let uu____8363 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8367 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8367)
                          in
                       if uu____8363
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
          let uu____8435 = FStar_Syntax_Util.head_and_args t  in
          match uu____8435 with
          | (hd1,uu____8451) ->
              let uu____8472 =
                let uu____8473 = FStar_Syntax_Subst.compress hd1  in
                uu____8473.FStar_Syntax_Syntax.n  in
              (match uu____8472 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8477) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8511  ->
                           match uu____8511 with
                           | (y,uu____8517) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8531  ->
                                       match uu____8531 with
                                       | (x,uu____8537) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8538 -> false)
           in
        let uu____8539 = rank tcenv p  in
        match uu____8539 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8546 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8573 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8587 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8601 -> false
  
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
                        let uu____8653 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8653 with
                        | (k,uu____8659) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8669 -> false)))
            | uu____8670 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8722 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8728 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8728 = (Prims.parse_int "0")))
                           in
                        if uu____8722 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8744 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8750 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8750 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8744)
               in
            let uu____8751 = filter1 u12  in
            let uu____8754 = filter1 u22  in (uu____8751, uu____8754)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8783 = filter_out_common_univs us1 us2  in
                (match uu____8783 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8842 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8842 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8845 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8855 =
                          let uu____8856 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8857 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8856
                            uu____8857
                           in
                        UFailed uu____8855))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8881 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8881 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8907 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8907 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8910 ->
                let uu____8915 =
                  let uu____8916 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8917 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8916
                    uu____8917 msg
                   in
                UFailed uu____8915
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8918,uu____8919) ->
              let uu____8920 =
                let uu____8921 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8922 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8921 uu____8922
                 in
              failwith uu____8920
          | (FStar_Syntax_Syntax.U_unknown ,uu____8923) ->
              let uu____8924 =
                let uu____8925 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8926 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8925 uu____8926
                 in
              failwith uu____8924
          | (uu____8927,FStar_Syntax_Syntax.U_bvar uu____8928) ->
              let uu____8929 =
                let uu____8930 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8931 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8930 uu____8931
                 in
              failwith uu____8929
          | (uu____8932,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8933 =
                let uu____8934 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8935 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8934 uu____8935
                 in
              failwith uu____8933
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8959 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8959
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8973 = occurs_univ v1 u3  in
              if uu____8973
              then
                let uu____8974 =
                  let uu____8975 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8976 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8975 uu____8976
                   in
                try_umax_components u11 u21 uu____8974
              else
                (let uu____8978 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8978)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8990 = occurs_univ v1 u3  in
              if uu____8990
              then
                let uu____8991 =
                  let uu____8992 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8993 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8992 uu____8993
                   in
                try_umax_components u11 u21 uu____8991
              else
                (let uu____8995 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8995)
          | (FStar_Syntax_Syntax.U_max uu____8996,uu____8997) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9003 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9003
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9005,FStar_Syntax_Syntax.U_max uu____9006) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9012 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9012
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9014,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9015,FStar_Syntax_Syntax.U_name
             uu____9016) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9017) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9018) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9019,FStar_Syntax_Syntax.U_succ
             uu____9020) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9021,FStar_Syntax_Syntax.U_zero
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
      let uu____9121 = bc1  in
      match uu____9121 with
      | (bs1,mk_cod1) ->
          let uu____9165 = bc2  in
          (match uu____9165 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9276 = aux xs ys  in
                     (match uu____9276 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9359 =
                       let uu____9366 = mk_cod1 xs  in ([], uu____9366)  in
                     let uu____9369 =
                       let uu____9376 = mk_cod2 ys  in ([], uu____9376)  in
                     (uu____9359, uu____9369)
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
                  let uu____9446 =
                    let uu____9447 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9447 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9446
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9452 = has_type_guard t1 t2  in (uu____9452, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9453 = has_type_guard t2 t1  in (uu____9453, wl)
  
let is_flex_pat :
  'Auu____9462 'Auu____9463 'Auu____9464 .
    ('Auu____9462,'Auu____9463,'Auu____9464 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___139_9477  ->
    match uu___139_9477 with
    | (uu____9486,uu____9487,[]) -> true
    | uu____9490 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9521 = f  in
      match uu____9521 with
      | (uu____9528,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9529;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9530;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9533;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9534;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9535;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9587  ->
                 match uu____9587 with
                 | (y,uu____9593) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9715 =
                  let uu____9728 =
                    let uu____9731 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9731  in
                  ((FStar_List.rev pat_binders), uu____9728)  in
                FStar_Pervasives_Native.Some uu____9715
            | (uu____9758,[]) ->
                let uu____9781 =
                  let uu____9794 =
                    let uu____9797 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9797  in
                  ((FStar_List.rev pat_binders), uu____9794)  in
                FStar_Pervasives_Native.Some uu____9781
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9862 =
                  let uu____9863 = FStar_Syntax_Subst.compress a  in
                  uu____9863.FStar_Syntax_Syntax.n  in
                (match uu____9862 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9881 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9881
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___167_9902 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___167_9902.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___167_9902.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9906 =
                            let uu____9907 =
                              let uu____9914 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9914)  in
                            FStar_Syntax_Syntax.NT uu____9907  in
                          [uu____9906]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___168_9926 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___168_9926.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___168_9926.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9927 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9955 =
                  let uu____9968 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9968  in
                (match uu____9955 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10031 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10058 ->
               let uu____10059 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10059 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10335 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10335
       then
         let uu____10336 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10336
       else ());
      (let uu____10338 = next_prob probs  in
       match uu____10338 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___169_10365 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___169_10365.wl_deferred);
               ctr = (uu___169_10365.ctr);
               defer_ok = (uu___169_10365.defer_ok);
               smt_ok = (uu___169_10365.smt_ok);
               tcenv = (uu___169_10365.tcenv);
               wl_implicits = (uu___169_10365.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10372 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10372
                then
                  let uu____10373 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10373
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
                          (let uu___170_10378 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___170_10378.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___170_10378.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___170_10378.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___170_10378.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___170_10378.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___170_10378.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___170_10378.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___170_10378.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___170_10378.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10400 ->
                let uu____10409 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10468  ->
                          match uu____10468 with
                          | (c,uu____10476,uu____10477) -> c < probs.ctr))
                   in
                (match uu____10409 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10518 =
                            let uu____10523 =
                              FStar_List.map
                                (fun uu____10538  ->
                                   match uu____10538 with
                                   | (uu____10549,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10523, (probs.wl_implicits))  in
                          Success uu____10518
                      | uu____10552 ->
                          let uu____10561 =
                            let uu___171_10562 = probs  in
                            let uu____10563 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10582  ->
                                      match uu____10582 with
                                      | (uu____10589,uu____10590,y) -> y))
                               in
                            {
                              attempting = uu____10563;
                              wl_deferred = rest;
                              ctr = (uu___171_10562.ctr);
                              defer_ok = (uu___171_10562.defer_ok);
                              smt_ok = (uu___171_10562.smt_ok);
                              tcenv = (uu___171_10562.tcenv);
                              wl_implicits = (uu___171_10562.wl_implicits)
                            }  in
                          solve env uu____10561))))

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
            let uu____10597 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10597 with
            | USolved wl1 ->
                let uu____10599 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10599
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
                  let uu____10651 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10651 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10654 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10666;
                  FStar_Syntax_Syntax.vars = uu____10667;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10670;
                  FStar_Syntax_Syntax.vars = uu____10671;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10683,uu____10684) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10691,FStar_Syntax_Syntax.Tm_uinst uu____10692) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10699 -> USolved wl

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
            ((let uu____10709 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10709
              then
                let uu____10710 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10710 msg
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
              let uu____10795 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10795 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10847 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10847
               then
                 let uu____10848 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10849 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                   uu____10848 uu____10849
               else ());
              (let uu____10851 = head_matches_delta env1 () t1 t2  in
               match uu____10851 with
               | (mr,ts1) ->
                   (match mr with
                    | HeadMatch (true ) ->
                        let uu____10896 = eq_prob t1 t2 wl2  in
                        (match uu____10896 with | (p,wl3) -> (t1, [p], wl3))
                    | MisMatch uu____10917 ->
                        let uu____10926 = eq_prob t1 t2 wl2  in
                        (match uu____10926 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch (false ) ->
                        let uu____10975 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10990 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10991 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10990, uu____10991)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10996 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10997 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10996, uu____10997)
                           in
                        (match uu____10975 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____11028 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____11028 with
                               | (t1_hd,t1_args) ->
                                   let uu____11067 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____11067 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____11121 =
                                             let uu____11128 =
                                               let uu____11137 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____11137 :: t1_args  in
                                             let uu____11150 =
                                               let uu____11157 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____11157 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____11198  ->
                                                  fun uu____11199  ->
                                                    fun uu____11200  ->
                                                      match (uu____11198,
                                                              uu____11199,
                                                              uu____11200)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____11242),
                                                         (a2,uu____11244)) ->
                                                          let uu____11269 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____11269
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____11128
                                               uu____11150
                                              in
                                           match uu____11121 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___172_11295 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___172_11295.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___172_11295.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11311 =
                                                 solve env1 wl'  in
                                               (match uu____11311 with
                                                | Success (uu____11314,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___173_11318 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___173_11318.attempting);
                                                           wl_deferred =
                                                             (uu___173_11318.wl_deferred);
                                                           ctr =
                                                             (uu___173_11318.ctr);
                                                           defer_ok =
                                                             (uu___173_11318.defer_ok);
                                                           smt_ok =
                                                             (uu___173_11318.smt_ok);
                                                           tcenv =
                                                             (uu___173_11318.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11327 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11359 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11359 with
                               | (t1_base,p1_opt) ->
                                   let uu____11406 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11406 with
                                    | (t2_base,p2_opt) ->
                                        let combine_refinements t_base
                                          p1_opt1 p2_opt1 =
                                          let refine1 x t =
                                            let uu____11516 = is_t_true t  in
                                            if uu____11516
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
                                              let uu____11564 =
                                                op phi11 phi21  in
                                              refine1 x1 uu____11564
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
                                              let uu____11594 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              refine1 x1 uu____11594
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
                                              let uu____11624 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              refine1 x1 uu____11624
                                          | uu____11627 -> t_base  in
                                        let uu____11644 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11644 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11658 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11658, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11665 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11665 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11712 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11712 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11759 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11759
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
                             let uu____11783 = combine t11 t21 wl2  in
                             (match uu____11783 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11816 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11816
                                    then
                                      let uu____11817 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11817
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11856 ts1 =
              match uu____11856 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11919 = pairwise out t wl2  in
                       (match uu____11919 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11955 =
              let uu____11966 = FStar_List.hd ts  in (uu____11966, [], wl1)
               in
            let uu____11975 = FStar_List.tl ts  in
            aux uu____11955 uu____11975  in
          let uu____11982 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11982 with
          | (this_flex,this_rigid) ->
              let uu____12006 =
                let uu____12007 = FStar_Syntax_Subst.compress this_rigid  in
                uu____12007.FStar_Syntax_Syntax.n  in
              (match uu____12006 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____12028 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____12028
                   then
                     let uu____12029 = destruct_flex_t this_flex wl  in
                     (match uu____12029 with
                      | (flex,wl1) ->
                          let uu____12036 = quasi_pattern env flex  in
                          (match uu____12036 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____12054 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____12054
                                 then
                                   let uu____12055 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____12055
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
                             ((let uu___174_12060 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___174_12060.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___174_12060.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___174_12060.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___174_12060.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___174_12060.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___174_12060.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___174_12060.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___174_12060.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___174_12060.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____12061 ->
                   ((let uu____12063 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____12063
                     then
                       let uu____12064 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____12064
                     else ());
                    (let uu____12066 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____12066 with
                     | (u,_args) ->
                         let uu____12103 =
                           let uu____12104 = FStar_Syntax_Subst.compress u
                              in
                           uu____12104.FStar_Syntax_Syntax.n  in
                         (match uu____12103 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____12135 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____12135 with
                                | (u',uu____12151) ->
                                    let uu____12172 =
                                      let uu____12173 = whnf env u'  in
                                      uu____12173.FStar_Syntax_Syntax.n  in
                                    (match uu____12172 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____12198 -> false)
                                 in
                              let uu____12199 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___140_12222  ->
                                        match uu___140_12222 with
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
                                             | uu____12231 -> false)
                                        | uu____12234 -> false))
                                 in
                              (match uu____12199 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____12248 = whnf env this_rigid
                                        in
                                     let uu____12249 =
                                       FStar_List.collect
                                         (fun uu___141_12255  ->
                                            match uu___141_12255 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____12261 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____12261]
                                            | uu____12263 -> []) bounds_probs
                                        in
                                     uu____12248 :: uu____12249  in
                                   let uu____12264 =
                                     let mk_conj1 t1 t2 =
                                       let uu____12296 = is_t_true t1  in
                                       if uu____12296
                                       then t2
                                       else
                                         (let uu____12300 = is_t_true t2  in
                                          if uu____12300
                                          then t1
                                          else
                                            FStar_Syntax_Util.mk_conj t1 t2)
                                        in
                                     let mk_disj1 t1 t2 =
                                       let uu____12325 = is_t_true t1  in
                                       if uu____12325
                                       then FStar_Syntax_Util.t_true
                                       else
                                         (let uu____12329 = is_t_true t2  in
                                          if uu____12329
                                          then FStar_Syntax_Util.t_true
                                          else
                                            FStar_Syntax_Util.mk_disj t1 t2)
                                        in
                                     meet_or_join
                                       (if flip then mk_conj1 else mk_disj1)
                                       bounds_typs env wl
                                      in
                                   (match uu____12264 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____12353 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____12368 =
                                              let uu____12369 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____12369.FStar_Syntax_Syntax.n
                                               in
                                            match uu____12368 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____12381 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____12381)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____12390 -> bound  in
                                          let uu____12391 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____12391)  in
                                        (match uu____12353 with
                                         | (bound_typ,(eq_prob,wl')) ->
                                             ((let uu____12419 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____12419
                                               then
                                                 let wl'1 =
                                                   let uu___175_12421 = wl1
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___175_12421.wl_deferred);
                                                     ctr =
                                                       (uu___175_12421.ctr);
                                                     defer_ok =
                                                       (uu___175_12421.defer_ok);
                                                     smt_ok =
                                                       (uu___175_12421.smt_ok);
                                                     tcenv =
                                                       (uu___175_12421.tcenv);
                                                     wl_implicits =
                                                       (uu___175_12421.wl_implicits)
                                                   }  in
                                                 let uu____12422 =
                                                   wl_to_string wl'1  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____12422
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____12425 =
                                                 solve_t env eq_prob
                                                   (let uu___176_12427 = wl'
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___176_12427.wl_deferred);
                                                      ctr =
                                                        (uu___176_12427.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___176_12427.smt_ok);
                                                      tcenv =
                                                        (uu___176_12427.tcenv);
                                                      wl_implicits =
                                                        (uu___176_12427.wl_implicits)
                                                    })
                                                  in
                                               match uu____12425 with
                                               | Success uu____12428 ->
                                                   let wl2 =
                                                     let uu___177_12434 = wl'
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___177_12434.wl_deferred);
                                                       ctr =
                                                         (uu___177_12434.ctr);
                                                       defer_ok =
                                                         (uu___177_12434.defer_ok);
                                                       smt_ok =
                                                         (uu___177_12434.smt_ok);
                                                       tcenv =
                                                         (uu___177_12434.tcenv);
                                                       wl_implicits =
                                                         (uu___177_12434.wl_implicits)
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
                                                   let uu____12449 =
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
                                                    (let uu____12461 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12461
                                                     then
                                                       let uu____12462 =
                                                         let uu____12463 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12463
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12462
                                                     else ());
                                                    (let uu____12469 =
                                                       let uu____12484 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12484)
                                                        in
                                                     match uu____12469 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12506))
                                                         ->
                                                         let uu____12531 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12531
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
                                                         let uu____12570 =
                                                           new_problem wl1
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12570
                                                          with
                                                          | (eq_prob1,wl2) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl2 tp x
                                                                  phi
                                                                 in
                                                              let wl3 =
                                                                let uu____12587
                                                                  =
                                                                  let uu____12592
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12592
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12587
                                                                  [] wl2
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl3))
                                                     | uu____12597 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12612 when flip ->
                              let uu____12613 =
                                let uu____12614 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12615 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12614 uu____12615
                                 in
                              failwith uu____12613
                          | uu____12616 ->
                              let uu____12617 =
                                let uu____12618 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12619 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12618 uu____12619
                                 in
                              failwith uu____12617))))

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
                      (fun uu____12647  ->
                         match uu____12647 with
                         | (x,i) ->
                             let uu____12658 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12658, i)) bs_lhs
                     in
                  let uu____12659 = lhs  in
                  match uu____12659 with
                  | (uu____12660,u_lhs,uu____12662) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12775 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12785 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12785, univ)
                             in
                          match uu____12775 with
                          | (k,univ) ->
                              let uu____12794 =
                                let uu____12801 =
                                  let uu____12804 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12804
                                   in
                                copy_uvar u_lhs uu____12801 wl2  in
                              (match uu____12794 with
                               | (uu____12817,u,wl3) ->
                                   let uu____12820 =
                                     let uu____12823 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12823
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12820, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12859 =
                              let uu____12872 =
                                let uu____12881 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12881 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12927  ->
                                   fun uu____12928  ->
                                     match (uu____12927, uu____12928) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13019 =
                                           let uu____13026 =
                                             let uu____13029 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13029
                                              in
                                           copy_uvar u_lhs uu____13026 wl2
                                            in
                                         (match uu____13019 with
                                          | (uu____13052,t_a,wl3) ->
                                              let uu____13055 =
                                                let uu____13062 =
                                                  let uu____13065 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____13065
                                                   in
                                                copy_uvar u_lhs uu____13062
                                                  wl3
                                                 in
                                              (match uu____13055 with
                                               | (uu____13080,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12872
                                ([], wl1)
                               in
                            (match uu____12859 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___178_13141 = ct  in
                                   let uu____13142 =
                                     let uu____13145 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13145
                                      in
                                   let uu____13160 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___178_13141.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___178_13141.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13142;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13160;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___178_13141.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___179_13178 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___179_13178.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___179_13178.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13181 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13181 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13235 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13235 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13252 =
                                          let uu____13257 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13257)  in
                                        TERM uu____13252  in
                                      let uu____13258 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13258 with
                                       | (sub_prob,wl3) ->
                                           let uu____13269 =
                                             let uu____13270 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13270
                                              in
                                           solve env uu____13269))
                             | (x,imp)::formals2 ->
                                 let uu____13284 =
                                   let uu____13291 =
                                     let uu____13294 =
                                       let uu____13297 =
                                         let uu____13298 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____13298
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____13297
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____13294
                                      in
                                   copy_uvar u_lhs uu____13291 wl1  in
                                 (match uu____13284 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____13322 =
                                          let uu____13325 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13325
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13322 t_y
                                         in
                                      let uu____13326 =
                                        let uu____13329 =
                                          let uu____13332 =
                                            let uu____13333 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13333, imp)  in
                                          [uu____13332]  in
                                        FStar_List.append bs_terms
                                          uu____13329
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13326 formals2 wl2)
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
              (let uu____13375 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13375
               then
                 let uu____13376 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13377 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13376 (rel_to_string (p_rel orig)) uu____13377
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13482 = rhs wl1 scope env1 subst1  in
                     (match uu____13482 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13502 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13502
                            then
                              let uu____13503 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13503
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___180_13557 = hd1  in
                       let uu____13558 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___180_13557.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___180_13557.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13558
                       }  in
                     let hd21 =
                       let uu___181_13562 = hd2  in
                       let uu____13563 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___181_13562.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___181_13562.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13563
                       }  in
                     let uu____13566 =
                       let uu____13571 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13571
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13566 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13590 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13590
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13594 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13594 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13649 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13649
                                  in
                               ((let uu____13661 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13661
                                 then
                                   let uu____13662 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13663 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13662
                                     uu____13663
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13690 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13719 = aux wl [] env [] bs1 bs2  in
               match uu____13719 with
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
        (let uu____13770 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13770 wl)

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
              let uu____13784 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13784 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13814 = lhs1  in
              match uu____13814 with
              | (uu____13817,ctx_u,uu____13819) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13825 ->
                        let uu____13826 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13826 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13873 = quasi_pattern env1 lhs1  in
              match uu____13873 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13903) ->
                  let uu____13908 = lhs1  in
                  (match uu____13908 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13922 = occurs_check ctx_u rhs1  in
                       (match uu____13922 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13964 =
                                let uu____13971 =
                                  let uu____13972 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13972
                                   in
                                FStar_Util.Inl uu____13971  in
                              (uu____13964, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13992 =
                                 let uu____13993 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13993  in
                               if uu____13992
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14013 =
                                    let uu____14020 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14020  in
                                  let uu____14025 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14013, uu____14025)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14087  ->
                     match uu____14087 with
                     | (x,i) ->
                         let uu____14098 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14098, i)) bs_lhs
                 in
              let uu____14099 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14099 with
              | (rhs_hd,args) ->
                  let uu____14136 = FStar_Util.prefix args  in
                  (match uu____14136 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14194 = lhs1  in
                       (match uu____14194 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14198 =
                              let uu____14209 =
                                let uu____14216 =
                                  let uu____14219 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14219
                                   in
                                copy_uvar u_lhs uu____14216 wl1  in
                              match uu____14209 with
                              | (uu____14240,t_last_arg,wl2) ->
                                  let uu____14243 =
                                    let uu____14250 =
                                      let uu____14253 =
                                        let uu____14260 =
                                          let uu____14267 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____14267]  in
                                        FStar_List.append bs_lhs uu____14260
                                         in
                                      let uu____14284 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____14253
                                        uu____14284
                                       in
                                    copy_uvar u_lhs uu____14250 wl2  in
                                  (match uu____14243 with
                                   | (uu____14297,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14303 =
                                         let uu____14310 =
                                           let uu____14313 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____14313
                                            in
                                         copy_uvar u_lhs uu____14310 wl3  in
                                       (match uu____14303 with
                                        | (uu____14326,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14198 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14350 =
                                     let uu____14351 =
                                       let uu____14356 =
                                         let uu____14357 =
                                           let uu____14360 =
                                             let uu____14365 =
                                               let uu____14366 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14366]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14365
                                              in
                                           uu____14360
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14357
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14356)  in
                                     TERM uu____14351  in
                                   [uu____14350]  in
                                 let uu____14387 =
                                   let uu____14394 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14394 with
                                   | (p1,wl3) ->
                                       let uu____14411 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14411 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14387 with
                                  | (sub_probs,wl3) ->
                                      let uu____14438 =
                                        let uu____14439 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14439  in
                                      solve env1 uu____14438))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14472 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14472 with
                | (uu____14487,args) ->
                    (match args with | [] -> false | uu____14515 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14530 =
                  let uu____14531 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14531.FStar_Syntax_Syntax.n  in
                match uu____14530 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14534 -> true
                | uu____14547 -> false  in
              let uu____14548 = quasi_pattern env1 lhs1  in
              match uu____14548 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14559 =
                    let uu____14560 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14560
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14559
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14567 = is_app rhs1  in
                  if uu____14567
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14569 = is_arrow rhs1  in
                     if uu____14569
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14571 =
                          let uu____14572 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14572
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14571))
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
                let uu____14575 = lhs  in
                (match uu____14575 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14579 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14579 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14594 =
                              let uu____14597 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14597
                               in
                            FStar_All.pipe_right uu____14594
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14612 = occurs_check ctx_uv rhs1  in
                          (match uu____14612 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14634 =
                                   let uu____14635 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14635
                                    in
                                 giveup_or_defer env orig wl uu____14634
                               else
                                 (let uu____14637 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14637
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14642 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14642
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14644 =
                                         let uu____14645 =
                                           names_to_string1 fvs2  in
                                         let uu____14646 =
                                           names_to_string1 fvs1  in
                                         let uu____14647 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14645 uu____14646
                                           uu____14647
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14644)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14653 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14657 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14657 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14680 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14680
                             | (FStar_Util.Inl msg,uu____14682) ->
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
                  (let uu____14711 =
                     let uu____14728 = quasi_pattern env lhs  in
                     let uu____14735 = quasi_pattern env rhs  in
                     (uu____14728, uu____14735)  in
                   match uu____14711 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14778 = lhs  in
                       (match uu____14778 with
                        | ({ FStar_Syntax_Syntax.n = uu____14779;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14781;_},u_lhs,uu____14783)
                            ->
                            let uu____14786 = rhs  in
                            (match uu____14786 with
                             | (uu____14787,u_rhs,uu____14789) ->
                                 let uu____14790 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14790
                                 then
                                   let uu____14791 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14791
                                 else
                                   (let uu____14793 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14793 with
                                    | (sub_prob,wl1) ->
                                        let uu____14804 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14804 with
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
                                             let uu____14832 =
                                               let uu____14839 =
                                                 let uu____14842 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14842
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
                                                 uu____14839
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14832 with
                                              | (uu____14845,w,wl2) ->
                                                  let w_app =
                                                    let uu____14851 =
                                                      let uu____14856 =
                                                        FStar_List.map
                                                          (fun uu____14865 
                                                             ->
                                                             match uu____14865
                                                             with
                                                             | (z,uu____14871)
                                                                 ->
                                                                 let uu____14872
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14872)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14856
                                                       in
                                                    uu____14851
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14876 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14876
                                                    then
                                                      let uu____14877 =
                                                        let uu____14880 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14881 =
                                                          let uu____14884 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14885 =
                                                            let uu____14888 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14889 =
                                                              let uu____14892
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14897
                                                                =
                                                                let uu____14900
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14905
                                                                  =
                                                                  let uu____14908
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14908]
                                                                   in
                                                                uu____14900
                                                                  ::
                                                                  uu____14905
                                                                 in
                                                              uu____14892 ::
                                                                uu____14897
                                                               in
                                                            uu____14888 ::
                                                              uu____14889
                                                             in
                                                          uu____14884 ::
                                                            uu____14885
                                                           in
                                                        uu____14880 ::
                                                          uu____14881
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14877
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14914 =
                                                          let uu____14919 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14919)
                                                           in
                                                        TERM uu____14914  in
                                                      let uu____14920 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14920
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14925 =
                                                             let uu____14930
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
                                                               uu____14930)
                                                              in
                                                           TERM uu____14925
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14931 =
                                                      let uu____14932 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14932
                                                       in
                                                    solve env uu____14931)))))))
                   | uu____14933 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14997 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14997
            then
              let uu____14998 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14999 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15000 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15001 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14998 uu____14999 uu____15000 uu____15001
            else ());
           (let uu____15005 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15005
            then
              let uu____15006 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15007 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15008 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15009 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____15006 uu____15007 uu____15008 uu____15009
            else ());
           (let uu____15011 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15011 with
            | (head1,args1) ->
                let uu____15048 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15048 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15102 =
                         let uu____15103 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15104 = args_to_string args1  in
                         let uu____15105 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15106 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15103 uu____15104 uu____15105 uu____15106
                          in
                       giveup env1 uu____15102 orig
                     else
                       (let uu____15108 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15114 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15114 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15108
                        then
                          let uu____15115 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____15115 with
                          | USolved wl2 ->
                              let uu____15117 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____15117
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____15121 = base_and_refinement env1 t1  in
                           match uu____15121 with
                           | (base1,refinement1) ->
                               let uu____15146 = base_and_refinement env1 t2
                                  in
                               (match uu____15146 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15203 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15203 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15207 =
                                                FStar_List.fold_right2
                                                  (fun uu____15240  ->
                                                     fun uu____15241  ->
                                                       fun uu____15242  ->
                                                         match (uu____15240,
                                                                 uu____15241,
                                                                 uu____15242)
                                                         with
                                                         | ((a,uu____15278),
                                                            (a',uu____15280),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15301
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15301
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15207 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15329 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15329
                                                     then
                                                       let uu____15330 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15330
                                                     else ());
                                                    (let formula =
                                                       let uu____15335 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15335
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     solve env1
                                                       (attempt subprobs wl4)))))
                                     | uu____15343 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___182_15383 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___182_15383.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___182_15383.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___182_15383.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___182_15383.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___182_15383.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___182_15383.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___182_15383.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___182_15383.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15421 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15421
            then
              let uu____15422 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15423 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15424 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15425 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15422 uu____15423 uu____15424 uu____15425
            else ());
           (let uu____15427 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15427 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15458,uu____15459) ->
                     let rec may_relate head3 =
                       let uu____15486 =
                         let uu____15487 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15487.FStar_Syntax_Syntax.n  in
                       match uu____15486 with
                       | FStar_Syntax_Syntax.Tm_name uu____15490 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15491 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15514;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15515;
                             FStar_Syntax_Syntax.fv_qual = uu____15516;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15519;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15520;
                             FStar_Syntax_Syntax.fv_qual = uu____15521;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15525,uu____15526) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15568) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15574) ->
                           may_relate t
                       | uu____15579 -> false  in
                     let uu____15580 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15580
                     then
                       let uu____15581 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15581 with
                        | (guard,wl2) ->
                            let uu____15588 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15588)
                     else
                       (let uu____15590 =
                          let uu____15591 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15592 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15591 uu____15592
                           in
                        giveup env1 uu____15590 orig)
                 | (HeadMatch (true ),uu____15593) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____15606 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15606 with
                        | (guard,wl2) ->
                            let uu____15613 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15613)
                     else
                       (let uu____15615 =
                          let uu____15616 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____15617 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____15616 uu____15617
                           in
                        giveup env1 uu____15615 orig)
                 | (uu____15618,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___183_15632 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___183_15632.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___183_15632.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___183_15632.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___183_15632.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___183_15632.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___183_15632.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___183_15632.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___183_15632.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15656 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15656
          then
            let uu____15657 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15657
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15662 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15662
              then
                let uu____15663 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15664 =
                  let uu____15665 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15666 =
                    let uu____15667 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15667  in
                  Prims.strcat uu____15665 uu____15666  in
                let uu____15668 =
                  let uu____15669 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15670 =
                    let uu____15671 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15671  in
                  Prims.strcat uu____15669 uu____15670  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15663
                  uu____15664 uu____15668
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15674,uu____15675) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15700,FStar_Syntax_Syntax.Tm_delayed uu____15701) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15726,uu____15727) ->
                  let uu____15754 =
                    let uu___184_15755 = problem  in
                    let uu____15756 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___184_15755.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15756;
                      FStar_TypeChecker_Common.relation =
                        (uu___184_15755.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___184_15755.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___184_15755.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___184_15755.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___184_15755.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___184_15755.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___184_15755.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___184_15755.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15754 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15757,uu____15758) ->
                  let uu____15765 =
                    let uu___185_15766 = problem  in
                    let uu____15767 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___185_15766.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15767;
                      FStar_TypeChecker_Common.relation =
                        (uu___185_15766.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___185_15766.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___185_15766.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___185_15766.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___185_15766.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___185_15766.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___185_15766.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___185_15766.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15765 wl
              | (uu____15768,FStar_Syntax_Syntax.Tm_ascribed uu____15769) ->
                  let uu____15796 =
                    let uu___186_15797 = problem  in
                    let uu____15798 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___186_15797.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___186_15797.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___186_15797.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15798;
                      FStar_TypeChecker_Common.element =
                        (uu___186_15797.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___186_15797.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___186_15797.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___186_15797.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___186_15797.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___186_15797.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15796 wl
              | (uu____15799,FStar_Syntax_Syntax.Tm_meta uu____15800) ->
                  let uu____15807 =
                    let uu___187_15808 = problem  in
                    let uu____15809 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___187_15808.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___187_15808.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___187_15808.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15809;
                      FStar_TypeChecker_Common.element =
                        (uu___187_15808.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___187_15808.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___187_15808.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___187_15808.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___187_15808.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___187_15808.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15807 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15811),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15813)) ->
                  let uu____15822 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15822
              | (FStar_Syntax_Syntax.Tm_bvar uu____15823,uu____15824) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15825,FStar_Syntax_Syntax.Tm_bvar uu____15826) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___142_15885 =
                    match uu___142_15885 with
                    | [] -> c
                    | bs ->
                        let uu____15907 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15907
                     in
                  let uu____15916 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15916 with
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
                                    let uu____16039 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____16039
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
                  let mk_t t l uu___143_16114 =
                    match uu___143_16114 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____16148 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____16148 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16267 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16268 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16267
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16268 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16269,uu____16270) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16297 -> true
                    | uu____16314 -> false  in
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
                      (let uu____16367 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___188_16375 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___188_16375.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___188_16375.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___188_16375.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___188_16375.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___188_16375.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___188_16375.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___188_16375.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___188_16375.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___188_16375.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___188_16375.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___188_16375.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___188_16375.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___188_16375.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___188_16375.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___188_16375.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___188_16375.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___188_16375.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___188_16375.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___188_16375.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___188_16375.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___188_16375.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___188_16375.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___188_16375.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___188_16375.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___188_16375.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___188_16375.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___188_16375.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___188_16375.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___188_16375.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___188_16375.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___188_16375.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___188_16375.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___188_16375.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___188_16375.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___188_16375.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___188_16375.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16367 with
                       | (uu____16378,ty,uu____16380) ->
                           let uu____16381 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16381)
                     in
                  let uu____16382 =
                    let uu____16399 = maybe_eta t1  in
                    let uu____16406 = maybe_eta t2  in
                    (uu____16399, uu____16406)  in
                  (match uu____16382 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___189_16448 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___189_16448.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___189_16448.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___189_16448.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___189_16448.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___189_16448.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___189_16448.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___189_16448.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___189_16448.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16469 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16469
                       then
                         let uu____16470 = destruct_flex_t not_abs wl  in
                         (match uu____16470 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16485 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16485.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16485.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16485.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16485.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16485.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16485.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16485.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16485.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16507 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16507
                       then
                         let uu____16508 = destruct_flex_t not_abs wl  in
                         (match uu____16508 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16523 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16523.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16523.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16523.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16523.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16523.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16523.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16523.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16523.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16525 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16542,FStar_Syntax_Syntax.Tm_abs uu____16543) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16570 -> true
                    | uu____16587 -> false  in
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
                      (let uu____16640 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___188_16648 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___188_16648.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___188_16648.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___188_16648.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___188_16648.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___188_16648.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___188_16648.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___188_16648.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___188_16648.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___188_16648.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___188_16648.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___188_16648.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___188_16648.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___188_16648.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___188_16648.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___188_16648.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___188_16648.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___188_16648.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___188_16648.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___188_16648.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___188_16648.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___188_16648.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___188_16648.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___188_16648.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___188_16648.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___188_16648.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___188_16648.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___188_16648.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___188_16648.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___188_16648.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___188_16648.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___188_16648.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___188_16648.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___188_16648.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___188_16648.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___188_16648.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___188_16648.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16640 with
                       | (uu____16651,ty,uu____16653) ->
                           let uu____16654 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16654)
                     in
                  let uu____16655 =
                    let uu____16672 = maybe_eta t1  in
                    let uu____16679 = maybe_eta t2  in
                    (uu____16672, uu____16679)  in
                  (match uu____16655 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___189_16721 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___189_16721.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___189_16721.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___189_16721.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___189_16721.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___189_16721.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___189_16721.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___189_16721.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___189_16721.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16742 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16742
                       then
                         let uu____16743 = destruct_flex_t not_abs wl  in
                         (match uu____16743 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16758 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16758.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16758.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16758.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16758.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16758.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16758.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16758.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16758.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16780 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16780
                       then
                         let uu____16781 = destruct_flex_t not_abs wl  in
                         (match uu____16781 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___190_16796 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___190_16796.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___190_16796.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___190_16796.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___190_16796.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___190_16796.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___190_16796.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___190_16796.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___190_16796.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16798 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16830 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16830) &&
                       (let uu____16834 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16834))
                      &&
                      (let uu____16841 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16841 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___144_16853 =
                             match uu___144_16853 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16854 -> true
                             | uu____16855 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16856 -> false)
                     in
                  let uu____16857 = as_refinement should_delta env wl t1  in
                  (match uu____16857 with
                   | (x11,phi1) ->
                       let uu____16870 = as_refinement should_delta env wl t2
                          in
                       (match uu____16870 with
                        | (x21,phi21) ->
                            let uu____16883 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16883 with
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
                                   let uu____16949 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16949
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16961 =
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
                                   (let uu____16975 =
                                      let uu____16976 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16976  in
                                    Prims.op_Negation uu____16975) ||
                                     (let uu____16980 =
                                        let uu____16981 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16981
                                         in
                                      Prims.op_Negation uu____16980)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16984 =
                                     let uu____16989 =
                                       let uu____16996 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16996]  in
                                     mk_t_problem wl1 uu____16989 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16984 with
                                    | (ref_prob,wl2) ->
                                        let uu____17011 =
                                          solve env1
                                            (let uu___191_17013 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___191_17013.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___191_17013.smt_ok);
                                               tcenv = (uu___191_17013.tcenv);
                                               wl_implicits =
                                                 (uu___191_17013.wl_implicits)
                                             })
                                           in
                                        (match uu____17011 with
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
                                         | Success uu____17023 ->
                                             let guard =
                                               let uu____17031 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____17031
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___192_17040 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___192_17040.attempting);
                                                 wl_deferred =
                                                   (uu___192_17040.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___192_17040.defer_ok);
                                                 smt_ok =
                                                   (uu___192_17040.smt_ok);
                                                 tcenv =
                                                   (uu___192_17040.tcenv);
                                                 wl_implicits =
                                                   (uu___192_17040.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17042,FStar_Syntax_Syntax.Tm_uvar uu____17043) ->
                  let uu____17072 = destruct_flex_t t1 wl  in
                  (match uu____17072 with
                   | (f1,wl1) ->
                       let uu____17079 = destruct_flex_t t2 wl1  in
                       (match uu____17079 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17086;
                    FStar_Syntax_Syntax.pos = uu____17087;
                    FStar_Syntax_Syntax.vars = uu____17088;_},uu____17089),FStar_Syntax_Syntax.Tm_uvar
                 uu____17090) ->
                  let uu____17139 = destruct_flex_t t1 wl  in
                  (match uu____17139 with
                   | (f1,wl1) ->
                       let uu____17146 = destruct_flex_t t2 wl1  in
                       (match uu____17146 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17153,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17154;
                    FStar_Syntax_Syntax.pos = uu____17155;
                    FStar_Syntax_Syntax.vars = uu____17156;_},uu____17157))
                  ->
                  let uu____17206 = destruct_flex_t t1 wl  in
                  (match uu____17206 with
                   | (f1,wl1) ->
                       let uu____17213 = destruct_flex_t t2 wl1  in
                       (match uu____17213 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17220;
                    FStar_Syntax_Syntax.pos = uu____17221;
                    FStar_Syntax_Syntax.vars = uu____17222;_},uu____17223),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17224;
                    FStar_Syntax_Syntax.pos = uu____17225;
                    FStar_Syntax_Syntax.vars = uu____17226;_},uu____17227))
                  ->
                  let uu____17296 = destruct_flex_t t1 wl  in
                  (match uu____17296 with
                   | (f1,wl1) ->
                       let uu____17303 = destruct_flex_t t2 wl1  in
                       (match uu____17303 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____17310,uu____17311) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17326 = destruct_flex_t t1 wl  in
                  (match uu____17326 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17333;
                    FStar_Syntax_Syntax.pos = uu____17334;
                    FStar_Syntax_Syntax.vars = uu____17335;_},uu____17336),uu____17337)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17372 = destruct_flex_t t1 wl  in
                  (match uu____17372 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17379,FStar_Syntax_Syntax.Tm_uvar uu____17380) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17395,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17396;
                    FStar_Syntax_Syntax.pos = uu____17397;
                    FStar_Syntax_Syntax.vars = uu____17398;_},uu____17399))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17434,FStar_Syntax_Syntax.Tm_arrow uu____17435) ->
                  solve_t' env
                    (let uu___193_17463 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___193_17463.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___193_17463.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___193_17463.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___193_17463.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___193_17463.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___193_17463.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___193_17463.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___193_17463.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___193_17463.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17464;
                    FStar_Syntax_Syntax.pos = uu____17465;
                    FStar_Syntax_Syntax.vars = uu____17466;_},uu____17467),FStar_Syntax_Syntax.Tm_arrow
                 uu____17468) ->
                  solve_t' env
                    (let uu___193_17516 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___193_17516.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___193_17516.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___193_17516.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___193_17516.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___193_17516.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___193_17516.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___193_17516.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___193_17516.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___193_17516.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17517,FStar_Syntax_Syntax.Tm_uvar uu____17518) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____17533,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17534;
                    FStar_Syntax_Syntax.pos = uu____17535;
                    FStar_Syntax_Syntax.vars = uu____17536;_},uu____17537))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____17572,uu____17573) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17588;
                    FStar_Syntax_Syntax.pos = uu____17589;
                    FStar_Syntax_Syntax.vars = uu____17590;_},uu____17591),uu____17592)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17627,uu____17628) ->
                  let t21 =
                    let uu____17636 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17636  in
                  solve_t env
                    (let uu___194_17662 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___194_17662.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___194_17662.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___194_17662.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___194_17662.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___194_17662.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___194_17662.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___194_17662.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___194_17662.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___194_17662.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17663,FStar_Syntax_Syntax.Tm_refine uu____17664) ->
                  let t11 =
                    let uu____17672 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17672  in
                  solve_t env
                    (let uu___195_17698 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17698.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___195_17698.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17698.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17698.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17698.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17698.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17698.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17698.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17698.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17780 =
                    let uu____17781 = guard_of_prob env wl problem t1 t2  in
                    match uu____17781 with
                    | (guard,wl1) ->
                        let uu____17788 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17788
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____17999 = br1  in
                        (match uu____17999 with
                         | (p1,w1,uu____18024) ->
                             let uu____18041 = br2  in
                             (match uu____18041 with
                              | (p2,w2,uu____18060) ->
                                  let uu____18065 =
                                    let uu____18066 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____18066  in
                                  if uu____18065
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____18082 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____18082 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____18115 = br2  in
                                         (match uu____18115 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____18150 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____18150
                                                 in
                                              let uu____18161 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____18184,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____18201) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____18244 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____18244 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____18161
                                                (fun uu____18286  ->
                                                   match uu____18286 with
                                                   | (wprobs,wl2) ->
                                                       let uu____18307 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____18307
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____18322 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____18322
                                                              (fun
                                                                 uu____18346 
                                                                 ->
                                                                 match uu____18346
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18431 -> FStar_Pervasives_Native.None  in
                  let uu____18468 = solve_branches wl brs1 brs2  in
                  (match uu____18468 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18496 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18496 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18513 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18513  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18522 =
                              solve env
                                (attempt sub_probs1
                                   (let uu___196_18524 = wl3  in
                                    {
                                      attempting =
                                        (uu___196_18524.attempting);
                                      wl_deferred =
                                        (uu___196_18524.wl_deferred);
                                      ctr = (uu___196_18524.ctr);
                                      defer_ok = (uu___196_18524.defer_ok);
                                      smt_ok = false;
                                      tcenv = (uu___196_18524.tcenv);
                                      wl_implicits =
                                        (uu___196_18524.wl_implicits)
                                    }))
                               in
                            (match uu____18522 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____18528 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____18534,uu____18535) ->
                  let head1 =
                    let uu____18559 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18559
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18599 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18599
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18639 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18639
                    then
                      let uu____18640 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18641 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18642 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18640 uu____18641 uu____18642
                    else ());
                   (let uu____18644 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18644
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18651 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18651
                       then
                         let uu____18652 =
                           let uu____18659 =
                             let uu____18660 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18660 = FStar_Syntax_Util.Equal  in
                           if uu____18659
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18670 = mk_eq2 wl orig t1 t2  in
                              match uu____18670 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18652 with
                         | (guard,wl1) ->
                             let uu____18691 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18691
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18694,uu____18695) ->
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
              | (FStar_Syntax_Syntax.Tm_name uu____18838,uu____18839) ->
                  let head1 =
                    let uu____18841 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18841
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18881 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18881
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18921 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18921
                    then
                      let uu____18922 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18923 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18924 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18922 uu____18923 uu____18924
                    else ());
                   (let uu____18926 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18926
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18933 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18933
                       then
                         let uu____18934 =
                           let uu____18941 =
                             let uu____18942 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18942 = FStar_Syntax_Util.Equal  in
                           if uu____18941
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18952 = mk_eq2 wl orig t1 t2  in
                              match uu____18952 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18934 with
                         | (guard,wl1) ->
                             let uu____18973 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18973
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18976,uu____18977) ->
                  let head1 =
                    let uu____18979 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18979
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19019 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19019
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19059 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19059
                    then
                      let uu____19060 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19061 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19062 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19060 uu____19061 uu____19062
                    else ());
                   (let uu____19064 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19064
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19071 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19071
                       then
                         let uu____19072 =
                           let uu____19079 =
                             let uu____19080 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19080 = FStar_Syntax_Util.Equal  in
                           if uu____19079
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19090 = mk_eq2 wl orig t1 t2  in
                              match uu____19090 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19072 with
                         | (guard,wl1) ->
                             let uu____19111 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19111
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____19114,uu____19115) ->
                  let head1 =
                    let uu____19117 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19117
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19157 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19157
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19197 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19197
                    then
                      let uu____19198 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19199 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19200 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19198 uu____19199 uu____19200
                    else ());
                   (let uu____19202 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19202
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19209 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19209
                       then
                         let uu____19210 =
                           let uu____19217 =
                             let uu____19218 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19218 = FStar_Syntax_Util.Equal  in
                           if uu____19217
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19228 = mk_eq2 wl orig t1 t2  in
                              match uu____19228 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19210 with
                         | (guard,wl1) ->
                             let uu____19249 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19249
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____19252,uu____19253) ->
                  let head1 =
                    let uu____19269 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19269
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19309 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19309
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19349 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19349
                    then
                      let uu____19350 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19351 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19352 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19350 uu____19351 uu____19352
                    else ());
                   (let uu____19354 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19354
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19361 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19361
                       then
                         let uu____19362 =
                           let uu____19369 =
                             let uu____19370 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19370 = FStar_Syntax_Util.Equal  in
                           if uu____19369
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19380 = mk_eq2 wl orig t1 t2  in
                              match uu____19380 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19362 with
                         | (guard,wl1) ->
                             let uu____19401 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19401
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19404,FStar_Syntax_Syntax.Tm_match uu____19405) ->
                  let head1 =
                    let uu____19429 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19429
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19469 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19469
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19509 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19509
                    then
                      let uu____19510 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19511 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19512 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19510 uu____19511 uu____19512
                    else ());
                   (let uu____19514 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19514
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19521 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19521
                       then
                         let uu____19522 =
                           let uu____19529 =
                             let uu____19530 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19530 = FStar_Syntax_Util.Equal  in
                           if uu____19529
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19540 = mk_eq2 wl orig t1 t2  in
                              match uu____19540 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19522 with
                         | (guard,wl1) ->
                             let uu____19561 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19561
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19564,FStar_Syntax_Syntax.Tm_uinst uu____19565) ->
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
              | (uu____19708,FStar_Syntax_Syntax.Tm_name uu____19709) ->
                  let head1 =
                    let uu____19711 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19711
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19751 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19751
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19791 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19791
                    then
                      let uu____19792 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19793 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19794 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19792 uu____19793 uu____19794
                    else ());
                   (let uu____19796 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19796
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19803 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19803
                       then
                         let uu____19804 =
                           let uu____19811 =
                             let uu____19812 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19812 = FStar_Syntax_Util.Equal  in
                           if uu____19811
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19822 = mk_eq2 wl orig t1 t2  in
                              match uu____19822 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19804 with
                         | (guard,wl1) ->
                             let uu____19843 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19843
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19846,FStar_Syntax_Syntax.Tm_constant uu____19847) ->
                  let head1 =
                    let uu____19849 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19849
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19883 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19883
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19917 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19917
                    then
                      let uu____19918 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19919 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19920 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19918 uu____19919 uu____19920
                    else ());
                   (let uu____19922 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19922
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19929 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19929
                       then
                         let uu____19930 =
                           let uu____19937 =
                             let uu____19938 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19938 = FStar_Syntax_Util.Equal  in
                           if uu____19937
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19948 = mk_eq2 wl orig t1 t2  in
                              match uu____19948 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19930 with
                         | (guard,wl1) ->
                             let uu____19969 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19969
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19972,FStar_Syntax_Syntax.Tm_fvar uu____19973) ->
                  let head1 =
                    let uu____19975 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19975
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20009 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20009
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20043 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20043
                    then
                      let uu____20044 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20045 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20046 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20044 uu____20045 uu____20046
                    else ());
                   (let uu____20048 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20048
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20055 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20055
                       then
                         let uu____20056 =
                           let uu____20063 =
                             let uu____20064 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20064 = FStar_Syntax_Util.Equal  in
                           if uu____20063
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20074 = mk_eq2 wl orig t1 t2  in
                              match uu____20074 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20056 with
                         | (guard,wl1) ->
                             let uu____20095 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20095
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____20098,FStar_Syntax_Syntax.Tm_app uu____20099) ->
                  let head1 =
                    let uu____20115 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20115
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20149 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20149
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20189 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20189
                    then
                      let uu____20190 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20191 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20192 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20190 uu____20191 uu____20192
                    else ());
                   (let uu____20194 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20194
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20201 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20201
                       then
                         let uu____20202 =
                           let uu____20209 =
                             let uu____20210 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20210 = FStar_Syntax_Util.Equal  in
                           if uu____20209
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20220 = mk_eq2 wl orig t1 t2  in
                              match uu____20220 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20202 with
                         | (guard,wl1) ->
                             let uu____20241 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20241
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____20244,FStar_Syntax_Syntax.Tm_let uu____20245) ->
                  let uu____20270 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____20270
                  then
                    let uu____20271 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____20271
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____20273,uu____20274) ->
                  let uu____20287 =
                    let uu____20292 =
                      let uu____20293 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20294 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20295 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20296 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20293 uu____20294 uu____20295 uu____20296
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20292)
                     in
                  FStar_Errors.raise_error uu____20287
                    t1.FStar_Syntax_Syntax.pos
              | (uu____20297,FStar_Syntax_Syntax.Tm_let uu____20298) ->
                  let uu____20311 =
                    let uu____20316 =
                      let uu____20317 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20318 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20319 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20320 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20317 uu____20318 uu____20319 uu____20320
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20316)
                     in
                  FStar_Errors.raise_error uu____20311
                    t1.FStar_Syntax_Syntax.pos
              | uu____20321 -> giveup env "head tag mismatch" orig))))

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
          (let uu____20380 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20380
           then
             let uu____20381 =
               let uu____20382 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____20382  in
             let uu____20383 =
               let uu____20384 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____20384  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____20381 uu____20383
           else ());
          (let uu____20386 =
             let uu____20387 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____20387  in
           if uu____20386
           then
             let uu____20388 =
               let uu____20389 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20390 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20389 uu____20390
                in
             giveup env uu____20388 orig
           else
             (let uu____20392 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____20392 with
              | (ret_sub_prob,wl1) ->
                  let uu____20399 =
                    FStar_List.fold_right2
                      (fun uu____20432  ->
                         fun uu____20433  ->
                           fun uu____20434  ->
                             match (uu____20432, uu____20433, uu____20434)
                             with
                             | ((a1,uu____20470),(a2,uu____20472),(arg_sub_probs,wl2))
                                 ->
                                 let uu____20493 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____20493 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____20399 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____20522 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____20522  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20552 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20555)::[] -> wp1
              | uu____20572 ->
                  let uu____20581 =
                    let uu____20582 =
                      let uu____20583 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20583  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20582
                     in
                  failwith uu____20581
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20589 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20589]
              | x -> x  in
            let uu____20591 =
              let uu____20600 =
                let uu____20607 =
                  let uu____20608 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20608 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20607  in
              [uu____20600]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20591;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20621 = lift_c1 ()  in solve_eq uu____20621 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___145_20627  ->
                       match uu___145_20627 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20628 -> false))
                in
             let uu____20629 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20655)::uu____20656,(wp2,uu____20658)::uu____20659)
                   -> (wp1, wp2)
               | uu____20712 ->
                   let uu____20733 =
                     let uu____20738 =
                       let uu____20739 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20740 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20739 uu____20740
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20738)
                      in
                   FStar_Errors.raise_error uu____20733
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20629 with
             | (wpc1,wpc2) ->
                 let uu____20747 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20747
                 then
                   let uu____20750 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20750 wl
                 else
                   (let uu____20752 =
                      let uu____20759 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20759  in
                    match uu____20752 with
                    | (c2_decl,qualifiers) ->
                        let uu____20780 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20780
                        then
                          let c1_repr =
                            let uu____20784 =
                              let uu____20785 =
                                let uu____20786 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20786  in
                              let uu____20787 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20785 uu____20787
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20784
                             in
                          let c2_repr =
                            let uu____20789 =
                              let uu____20790 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20791 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20790 uu____20791
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20789
                             in
                          let uu____20792 =
                            let uu____20797 =
                              let uu____20798 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20799 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20798 uu____20799
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20797
                             in
                          (match uu____20792 with
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
                                 ((let uu____20813 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20813
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20816 =
                                     let uu____20823 =
                                       let uu____20824 =
                                         let uu____20839 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20842 =
                                           let uu____20851 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20858 =
                                             let uu____20867 =
                                               let uu____20874 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20874
                                                in
                                             [uu____20867]  in
                                           uu____20851 :: uu____20858  in
                                         (uu____20839, uu____20842)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20824
                                        in
                                     FStar_Syntax_Syntax.mk uu____20823  in
                                   uu____20816 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20915 =
                                    let uu____20922 =
                                      let uu____20923 =
                                        let uu____20938 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20941 =
                                          let uu____20950 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20957 =
                                            let uu____20966 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20973 =
                                              let uu____20982 =
                                                let uu____20989 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20989
                                                 in
                                              [uu____20982]  in
                                            uu____20966 :: uu____20973  in
                                          uu____20950 :: uu____20957  in
                                        (uu____20938, uu____20941)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20923
                                       in
                                    FStar_Syntax_Syntax.mk uu____20922  in
                                  uu____20915 FStar_Pervasives_Native.None r)
                              in
                           let uu____21033 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____21033 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____21041 =
                                   let uu____21044 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____21044
                                    in
                                 solve_prob orig uu____21041 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____21047 = FStar_Util.physical_equality c1 c2  in
        if uu____21047
        then
          let uu____21048 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21048
        else
          ((let uu____21051 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21051
            then
              let uu____21052 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21053 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21052
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21053
            else ());
           (let uu____21055 =
              let uu____21064 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21067 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21064, uu____21067)  in
            match uu____21055 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21085),FStar_Syntax_Syntax.Total
                    (t2,uu____21087)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21104 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21104 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21105,FStar_Syntax_Syntax.Total uu____21106) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21124),FStar_Syntax_Syntax.Total
                    (t2,uu____21126)) ->
                     let uu____21143 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21143 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21145),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21147)) ->
                     let uu____21164 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21164 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21166),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21168)) ->
                     let uu____21185 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21185 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21186,FStar_Syntax_Syntax.Comp uu____21187) ->
                     let uu____21196 =
                       let uu___197_21199 = problem  in
                       let uu____21202 =
                         let uu____21203 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21203
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___197_21199.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21202;
                         FStar_TypeChecker_Common.relation =
                           (uu___197_21199.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___197_21199.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___197_21199.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___197_21199.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___197_21199.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___197_21199.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___197_21199.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___197_21199.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21196 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21204,FStar_Syntax_Syntax.Comp uu____21205) ->
                     let uu____21214 =
                       let uu___197_21217 = problem  in
                       let uu____21220 =
                         let uu____21221 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21221
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___197_21217.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21220;
                         FStar_TypeChecker_Common.relation =
                           (uu___197_21217.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___197_21217.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___197_21217.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___197_21217.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___197_21217.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___197_21217.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___197_21217.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___197_21217.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21214 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21222,FStar_Syntax_Syntax.GTotal uu____21223) ->
                     let uu____21232 =
                       let uu___198_21235 = problem  in
                       let uu____21238 =
                         let uu____21239 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21239
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___198_21235.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___198_21235.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___198_21235.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21238;
                         FStar_TypeChecker_Common.element =
                           (uu___198_21235.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___198_21235.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___198_21235.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___198_21235.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___198_21235.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___198_21235.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21232 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21240,FStar_Syntax_Syntax.Total uu____21241) ->
                     let uu____21250 =
                       let uu___198_21253 = problem  in
                       let uu____21256 =
                         let uu____21257 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21257
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___198_21253.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___198_21253.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___198_21253.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21256;
                         FStar_TypeChecker_Common.element =
                           (uu___198_21253.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___198_21253.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___198_21253.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___198_21253.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___198_21253.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___198_21253.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21250 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21258,FStar_Syntax_Syntax.Comp uu____21259) ->
                     let uu____21260 =
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
                     if uu____21260
                     then
                       let uu____21261 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21261 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21265 =
                            let uu____21270 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____21270
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21276 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21277 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21276, uu____21277))
                             in
                          match uu____21265 with
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
                           (let uu____21284 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21284
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21286 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21286 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21289 =
                                  let uu____21290 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21291 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21290 uu____21291
                                   in
                                giveup env uu____21289 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21298 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21326  ->
              match uu____21326 with
              | (uu____21335,tm,uu____21337,uu____21338) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____21298 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21371 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21371 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21389 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21417  ->
                match uu____21417 with
                | (u1,u2) ->
                    let uu____21424 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21425 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21424 uu____21425))
         in
      FStar_All.pipe_right uu____21389 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21452,[])) -> "{}"
      | uu____21477 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21500 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21500
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21503 =
              FStar_List.map
                (fun uu____21513  ->
                   match uu____21513 with
                   | (uu____21518,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21503 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21523 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21523 imps
  
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
                  let uu____21576 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21576
                  then
                    let uu____21577 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21578 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21577
                      (rel_to_string rel) uu____21578
                  else "TOP"  in
                let uu____21580 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21580 with
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
              let uu____21637 =
                let uu____21640 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21640
                 in
              FStar_Syntax_Syntax.new_bv uu____21637 t1  in
            let uu____21643 =
              let uu____21648 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21648
               in
            match uu____21643 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____21721 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21721
              then
                let uu____21722 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21722
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
          ((let uu____21744 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21744
            then
              let uu____21745 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21745
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21749 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21749
             then
               let uu____21750 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21750
             else ());
            (let f2 =
               let uu____21753 =
                 let uu____21754 = FStar_Syntax_Util.unmeta f1  in
                 uu____21754.FStar_Syntax_Syntax.n  in
               match uu____21753 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21758 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___199_21759 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___199_21759.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___199_21759.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___199_21759.FStar_TypeChecker_Env.implicits)
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
            let uu____21861 =
              let uu____21862 =
                let uu____21863 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21863;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21862  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21861
  
let with_guard_no_simp :
  'Auu____21878 .
    'Auu____21878 ->
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
            let uu____21901 =
              let uu____21902 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21902;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21901
  
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
          (let uu____21940 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21940
           then
             let uu____21941 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21942 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21941
               uu____21942
           else ());
          (let uu____21944 =
             let uu____21949 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____21949
              in
           match uu____21944 with
           | (prob,wl) ->
               let g =
                 let uu____21957 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21975  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21957  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22017 = try_teq true env t1 t2  in
        match uu____22017 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22021 = FStar_TypeChecker_Env.get_range env  in
              let uu____22022 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22021 uu____22022);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22029 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22029
              then
                let uu____22030 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22031 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22032 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22030
                  uu____22031 uu____22032
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
          let uu____22054 = FStar_TypeChecker_Env.get_range env  in
          let uu____22055 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22054 uu____22055
  
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
        (let uu____22080 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22080
         then
           let uu____22081 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22082 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____22081 uu____22082
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____22085 =
           let uu____22092 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____22092 "sub_comp"
            in
         match uu____22085 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____22102 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____22120  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____22102)
  
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
      fun uu____22173  ->
        match uu____22173 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22216 =
                 let uu____22221 =
                   let uu____22222 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22223 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22222 uu____22223
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22221)  in
               let uu____22224 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22216 uu____22224)
               in
            let equiv1 v1 v' =
              let uu____22236 =
                let uu____22241 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22242 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22241, uu____22242)  in
              match uu____22236 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22261 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22291 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22291 with
                      | FStar_Syntax_Syntax.U_unif uu____22298 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22327  ->
                                    match uu____22327 with
                                    | (u,v') ->
                                        let uu____22336 = equiv1 v1 v'  in
                                        if uu____22336
                                        then
                                          let uu____22339 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22339 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22355 -> []))
               in
            let uu____22360 =
              let wl =
                let uu___200_22364 = empty_worklist env  in
                {
                  attempting = (uu___200_22364.attempting);
                  wl_deferred = (uu___200_22364.wl_deferred);
                  ctr = (uu___200_22364.ctr);
                  defer_ok = false;
                  smt_ok = (uu___200_22364.smt_ok);
                  tcenv = (uu___200_22364.tcenv);
                  wl_implicits = (uu___200_22364.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22382  ->
                      match uu____22382 with
                      | (lb,v1) ->
                          let uu____22389 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22389 with
                           | USolved wl1 -> ()
                           | uu____22391 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22401 =
              match uu____22401 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22410) -> true
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
                      uu____22433,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22435,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22446) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22453,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22461 -> false)
               in
            let uu____22466 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22481  ->
                      match uu____22481 with
                      | (u,v1) ->
                          let uu____22488 = check_ineq (u, v1)  in
                          if uu____22488
                          then true
                          else
                            ((let uu____22491 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22491
                              then
                                let uu____22492 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22493 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22492
                                  uu____22493
                              else ());
                             false)))
               in
            if uu____22466
            then ()
            else
              ((let uu____22497 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22497
                then
                  ((let uu____22499 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22499);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22509 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22509))
                else ());
               (let uu____22519 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22519))
  
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
        let fail1 uu____22586 =
          match uu____22586 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___201_22607 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___201_22607.attempting);
            wl_deferred = (uu___201_22607.wl_deferred);
            ctr = (uu___201_22607.ctr);
            defer_ok;
            smt_ok = (uu___201_22607.smt_ok);
            tcenv = (uu___201_22607.tcenv);
            wl_implicits = (uu___201_22607.wl_implicits)
          }  in
        (let uu____22609 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22609
         then
           let uu____22610 = FStar_Util.string_of_bool defer_ok  in
           let uu____22611 = wl_to_string wl  in
           let uu____22612 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22610 uu____22611 uu____22612
         else ());
        (let g1 =
           let uu____22623 = solve_and_commit env wl fail1  in
           match uu____22623 with
           | FStar_Pervasives_Native.Some
               (uu____22630::uu____22631,uu____22632) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___202_22657 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___202_22657.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___202_22657.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22666 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___203_22674 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___203_22674.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___203_22674.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___203_22674.FStar_TypeChecker_Env.implicits)
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
    let uu____22722 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22722 with
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
            let uu___204_22845 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___204_22845.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___204_22845.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___204_22845.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22846 =
            let uu____22847 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22847  in
          if uu____22846
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22855 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22856 =
                       let uu____22857 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22857
                        in
                     FStar_Errors.diag uu____22855 uu____22856)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22861 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22862 =
                        let uu____22863 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22863
                         in
                      FStar_Errors.diag uu____22861 uu____22862)
                   else ();
                   (let uu____22866 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22866 "discharge_guard'"
                      env vc1);
                   (let uu____22867 = check_trivial vc1  in
                    match uu____22867 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22874 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22875 =
                                let uu____22876 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22876
                                 in
                              FStar_Errors.diag uu____22874 uu____22875)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22881 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22882 =
                                let uu____22883 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22883
                                 in
                              FStar_Errors.diag uu____22881 uu____22882)
                           else ();
                           (let vcs =
                              let uu____22896 = FStar_Options.use_tactics ()
                                 in
                              if uu____22896
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22918  ->
                                     (let uu____22920 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22920);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22963  ->
                                              match uu____22963 with
                                              | (env1,goal,opts) ->
                                                  let uu____22979 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22979, opts)))))
                              else
                                (let uu____22981 =
                                   let uu____22990 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22990)  in
                                 [uu____22981])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23033  ->
                                    match uu____23033 with
                                    | (env1,goal,opts) ->
                                        let uu____23049 = check_trivial goal
                                           in
                                        (match uu____23049 with
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
                                                (let uu____23057 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23058 =
                                                   let uu____23059 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____23060 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23059 uu____23060
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23057 uu____23058)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23063 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23064 =
                                                   let uu____23065 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23065
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23063 uu____23064)
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
      let uu____23079 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23079 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23086 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23086
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23097 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23097 with
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
            let uu____23130 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____23130 with
            | FStar_Pervasives_Native.Some uu____23133 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____23153 = acc  in
            match uu____23153 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____23205 = hd1  in
                     (match uu____23205 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23219 = unresolved ctx_u  in
                             if uu____23219
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___205_23231 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___205_23231.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___205_23231.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___205_23231.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___205_23231.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___205_23231.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___205_23231.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___205_23231.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___205_23231.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___205_23231.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___205_23231.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___205_23231.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___205_23231.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___205_23231.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___205_23231.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___205_23231.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___205_23231.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___205_23231.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___205_23231.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___205_23231.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___205_23231.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___205_23231.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___205_23231.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___205_23231.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___205_23231.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___205_23231.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___205_23231.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___205_23231.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___205_23231.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___205_23231.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___205_23231.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___205_23231.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___205_23231.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___205_23231.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___205_23231.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___205_23231.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___205_23231.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___205_23231.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___205_23231.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___206_23234 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___206_23234.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___206_23234.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___206_23234.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___206_23234.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___206_23234.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___206_23234.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___206_23234.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___206_23234.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___206_23234.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___206_23234.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___206_23234.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___206_23234.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___206_23234.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___206_23234.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___206_23234.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___206_23234.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___206_23234.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___206_23234.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___206_23234.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___206_23234.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___206_23234.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___206_23234.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___206_23234.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___206_23234.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___206_23234.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___206_23234.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___206_23234.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___206_23234.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___206_23234.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___206_23234.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___206_23234.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___206_23234.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___206_23234.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___206_23234.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___206_23234.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___206_23234.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___206_23234.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___206_23234.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____23237 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23237
                                   then
                                     let uu____23238 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____23239 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____23240 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____23241 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____23238 uu____23239 uu____23240
                                       reason uu____23241
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____23252 =
                                             let uu____23261 =
                                               let uu____23268 =
                                                 let uu____23269 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____23270 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____23271 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____23269 uu____23270
                                                   uu____23271
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____23268, r)
                                                in
                                             [uu____23261]  in
                                           FStar_Errors.add_errors
                                             uu____23252);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___209_23285 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___209_23285.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___209_23285.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___209_23285.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____23288 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____23298  ->
                                               let uu____23299 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____23300 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____23301 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____23299 uu____23300
                                                 reason uu____23301)) env2 g2
                                         true
                                        in
                                     match uu____23288 with
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
          let uu___210_23311 = g  in
          let uu____23312 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___210_23311.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___210_23311.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___210_23311.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23312
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
        let uu____23362 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23362 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23371 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23371
      | (reason,e,ctx_u,r)::uu____23376 ->
          let uu____23395 =
            let uu____23400 =
              let uu____23401 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23402 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23401 uu____23402 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23400)
             in
          FStar_Errors.raise_error uu____23395 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___211_23413 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___211_23413.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___211_23413.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___211_23413.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23428 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23428 with
      | FStar_Pervasives_Native.Some uu____23434 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23450 = try_teq false env t1 t2  in
        match uu____23450 with
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
        (let uu____23484 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23484
         then
           let uu____23485 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23486 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23485
             uu____23486
         else ());
        (let uu____23488 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23488 with
         | (prob,x,wl) ->
             let g =
               let uu____23507 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23525  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23507  in
             ((let uu____23553 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23553
               then
                 let uu____23554 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23555 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23556 =
                   let uu____23557 = FStar_Util.must g  in
                   guard_to_string env uu____23557  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23554 uu____23555 uu____23556
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
        let uu____23591 = check_subtyping env t1 t2  in
        match uu____23591 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23610 =
              let uu____23611 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23611 g  in
            FStar_Pervasives_Native.Some uu____23610
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23629 = check_subtyping env t1 t2  in
        match uu____23629 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23648 =
              let uu____23649 =
                let uu____23650 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23650]  in
              close_guard env uu____23649 g  in
            FStar_Pervasives_Native.Some uu____23648
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23679 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23679
         then
           let uu____23680 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23681 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23680
             uu____23681
         else ());
        (let uu____23683 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23683 with
         | (prob,x,wl) ->
             let g =
               let uu____23696 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23714  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23696  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23743 =
                      let uu____23744 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23744]  in
                    close_guard env uu____23743 g1  in
                  discharge_guard_nosmt env g2))
  