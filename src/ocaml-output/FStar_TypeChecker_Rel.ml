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
             (fun uu____90  ->
                match uu____90 with
                | (uu____101,uu____102,ctx_uvar,uu____104,uu____105) ->
                    let uu____106 =
                      FStar_Syntax_Unionfind.find
                        ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                       in
                    (match uu____106 with
                     | FStar_Pervasives_Native.Some uu____109 -> true
                     | FStar_Pervasives_Native.None  -> false)))
    | uu____110 -> false
  
let (is_trivial_guard_formula : FStar_TypeChecker_Env.guard_t -> Prims.bool)
  =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = uu____116;
        FStar_TypeChecker_Env.univ_ineqs = uu____117;
        FStar_TypeChecker_Env.implicits = uu____118;_} -> true
    | uu____139 -> false
  
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
          let uu___146_176 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___146_176.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___146_176.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___146_176.FStar_TypeChecker_Env.implicits)
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
          let uu____211 = FStar_Options.defensive ()  in
          if uu____211
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____215 =
              let uu____216 =
                let uu____217 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____217  in
              Prims.op_Negation uu____216  in
            (if uu____215
             then
               let uu____222 =
                 let uu____227 =
                   let uu____228 = FStar_Syntax_Print.term_to_string t  in
                   let uu____229 =
                     let uu____230 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____230
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____228 uu____229
                    in
                 (FStar_Errors.Warning_Defensive, uu____227)  in
               FStar_Errors.log_issue rng uu____222
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> unit) =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____252 =
          let uu____253 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____253  in
        if uu____252
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
          let uu____279 =
            let uu____280 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____280  in
          if uu____279
          then ()
          else
            (let uu____282 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____282 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____305 =
            let uu____306 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____306  in
          if uu____305
          then ()
          else
            (let uu____308 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____308 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___147_322 = g  in
          let uu____323 =
            let uu____324 =
              let uu____325 =
                let uu____332 =
                  let uu____333 =
                    let uu____348 =
                      let uu____357 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____357]  in
                    (f, uu____348)  in
                  FStar_Syntax_Syntax.Tm_app uu____333  in
                FStar_Syntax_Syntax.mk uu____332  in
              uu____325 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
              uu____324
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____323;
            FStar_TypeChecker_Env.deferred =
              (uu___147_322.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___147_322.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___147_322.FStar_TypeChecker_Env.implicits)
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
          let uu___148_405 = g  in
          let uu____406 =
            let uu____407 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____407  in
          {
            FStar_TypeChecker_Env.guard_f = uu____406;
            FStar_TypeChecker_Env.deferred =
              (uu___148_405.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___148_405.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___148_405.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____413 -> failwith "impossible"
  
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
          let uu____428 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____428
  
let (check_trivial :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Common.guard_formula)
  =
  fun t  ->
    let uu____438 =
      let uu____439 = FStar_Syntax_Util.unmeta t  in
      uu____439.FStar_Syntax_Syntax.n  in
    match uu____438 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____443 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____484 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____484;
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
                       let uu____571 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____571
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___149_573 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___149_573.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___149_573.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___149_573.FStar_TypeChecker_Env.implicits)
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
               let uu____614 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____614
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
            let uu___150_633 = g  in
            let uu____634 =
              let uu____635 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____635  in
            {
              FStar_TypeChecker_Env.guard_f = uu____634;
              FStar_TypeChecker_Env.deferred =
                (uu___150_633.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___150_633.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___150_633.FStar_TypeChecker_Env.implicits)
            }
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____664 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____694 -> false
  
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
                  let uu____981 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____981;
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
                   (let uu___151_1015 = wl  in
                    {
                      attempting = (uu___151_1015.attempting);
                      wl_deferred = (uu___151_1015.wl_deferred);
                      ctr = (uu___151_1015.ctr);
                      defer_ok = (uu___151_1015.defer_ok);
                      smt_ok = (uu___151_1015.smt_ok);
                      tcenv = (uu___151_1015.tcenv);
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
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____1079 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1109 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____1134 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1140 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1146 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___114_1161  ->
    match uu___114_1161 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1167 = FStar_Syntax_Util.head_and_args t  in
    match uu____1167 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1226 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1227 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1241 =
                     let uu____1242 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1242  in
                   FStar_Util.format1 "@<%s>" uu____1241
                in
             let uu____1245 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1226 uu____1227 uu____1245
         | uu____1246 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___115_1256  ->
      match uu___115_1256 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1260 =
            let uu____1263 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1264 =
              let uu____1267 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1268 =
                let uu____1271 =
                  let uu____1274 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1274]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1271
                 in
              uu____1267 :: uu____1268  in
            uu____1263 :: uu____1264  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1260
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1278 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1279 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1280 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1278 uu____1279
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1280
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___116_1290  ->
      match uu___116_1290 with
      | UNIV (u,t) ->
          let x =
            let uu____1294 = FStar_Options.hide_uvar_nums ()  in
            if uu____1294
            then "?"
            else
              (let uu____1296 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1296 FStar_Util.string_of_int)
             in
          let uu____1297 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1297
      | TERM (u,t) ->
          let x =
            let uu____1301 = FStar_Options.hide_uvar_nums ()  in
            if uu____1301
            then "?"
            else
              (let uu____1303 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1303 FStar_Util.string_of_int)
             in
          let uu____1304 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1304
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1319 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1319 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1333 =
      let uu____1336 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1336
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1333 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1349 .
    (FStar_Syntax_Syntax.term,'Auu____1349) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1367 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1385  ->
              match uu____1385 with
              | (x,uu____1391) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1367 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1399 =
      let uu____1400 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1400  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1399;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___152_1432 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___152_1432.wl_deferred);
          ctr = (uu___152_1432.ctr);
          defer_ok = (uu___152_1432.defer_ok);
          smt_ok;
          tcenv = (uu___152_1432.tcenv);
          wl_implicits = (uu___152_1432.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1439 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1439,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___153_1462 = empty_worklist env  in
      let uu____1463 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1463;
        wl_deferred = (uu___153_1462.wl_deferred);
        ctr = (uu___153_1462.ctr);
        defer_ok = (uu___153_1462.defer_ok);
        smt_ok = (uu___153_1462.smt_ok);
        tcenv = (uu___153_1462.tcenv);
        wl_implicits = (uu___153_1462.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___154_1483 = wl  in
        {
          attempting = (uu___154_1483.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___154_1483.ctr);
          defer_ok = (uu___154_1483.defer_ok);
          smt_ok = (uu___154_1483.smt_ok);
          tcenv = (uu___154_1483.tcenv);
          wl_implicits = (uu___154_1483.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___155_1504 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___155_1504.wl_deferred);
        ctr = (uu___155_1504.ctr);
        defer_ok = (uu___155_1504.defer_ok);
        smt_ok = (uu___155_1504.smt_ok);
        tcenv = (uu___155_1504.tcenv);
        wl_implicits = (uu___155_1504.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1521 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1521
         then
           let uu____1522 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1522
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___117_1528  ->
    match uu___117_1528 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1533 .
    'Auu____1533 FStar_TypeChecker_Common.problem ->
      'Auu____1533 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___156_1545 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___156_1545.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___156_1545.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___156_1545.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___156_1545.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___156_1545.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___156_1545.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___156_1545.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1552 .
    'Auu____1552 FStar_TypeChecker_Common.problem ->
      'Auu____1552 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___118_1569  ->
    match uu___118_1569 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.TProb _0_17)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.CProb _0_18)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___119_1584  ->
    match uu___119_1584 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___157_1590 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___157_1590.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___157_1590.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___157_1590.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___157_1590.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___157_1590.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___157_1590.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___157_1590.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___157_1590.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___157_1590.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___158_1598 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___158_1598.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___158_1598.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___158_1598.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___158_1598.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___158_1598.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___158_1598.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___158_1598.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___158_1598.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___158_1598.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___120_1610  ->
      match uu___120_1610 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___121_1615  ->
    match uu___121_1615 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___122_1626  ->
    match uu___122_1626 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___123_1639  ->
    match uu___123_1639 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___124_1652  ->
    match uu___124_1652 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___125_1663  ->
    match uu___125_1663 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___126_1678  ->
    match uu___126_1678 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1697 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1697) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1725 =
          let uu____1726 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1726  in
        if uu____1725
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1760)::bs ->
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
        let uu____1827 =
          let uu____1828 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1828  in
        if uu____1827
        then ()
        else
          (let uu____1830 =
             let uu____1833 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1833
              in
           def_check_closed_in (p_loc prob) msg uu____1830 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1863 =
         let uu____1864 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1864  in
       if uu____1863
       then ()
       else
         (let uu____1866 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1866));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1878 -> ())
  
let mk_eq2 :
  'Auu____1890 .
    worklist ->
      'Auu____1890 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1919 = FStar_Syntax_Util.type_u ()  in
          match uu____1919 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1931 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type false
                 in
              (match uu____1931 with
               | (uv,tt,wl1) ->
                   let uu____1945 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1945, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___127_1950  ->
    match uu___127_1950 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1966 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1966 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1978  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2076 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2076 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2076 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2076 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2142 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2142  in
                  let uu____2145 =
                    let uu____2152 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2152
                      guard_ty false
                     in
                  match uu____2145 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2173 ->
                            let uu____2180 =
                              let uu____2185 =
                                FStar_List.map
                                  (fun uu____2198  ->
                                     match uu____2198 with
                                     | (x,i) ->
                                         let uu____2209 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2209, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2185  in
                            uu____2180 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2212 =
                        let uu____2215 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2215;
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
                      (uu____2212, wl1)
  
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
                  let uu____2278 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2278 with
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
                  let uu____2355 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2355 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2390 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2390 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2390 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2390 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2441 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2496 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2496]  in
                        let uu____2509 =
                          let uu____2512 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2512  in
                        let uu____2515 =
                          let uu____2518 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2518  in
                        (bs, uu____2509, uu____2515)
                     in
                  match uu____2441 with
                  | (bs,lg_ty,elt) ->
                      let uu____2558 =
                        let uu____2565 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___159_2573 = wl  in
                           {
                             attempting = (uu___159_2573.attempting);
                             wl_deferred = (uu___159_2573.wl_deferred);
                             ctr = (uu___159_2573.ctr);
                             defer_ok = (uu___159_2573.defer_ok);
                             smt_ok = (uu___159_2573.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___159_2573.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2565
                          lg_ty false
                         in
                      (match uu____2558 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2585 =
                                   let uu____2590 =
                                     let uu____2591 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2591]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2590
                                    in
                                 uu____2585 FStar_Pervasives_Native.None loc
                              in
                           let uu____2612 =
                             let uu____2615 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2615;
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
                           (uu____2612, wl1))
  
let problem_using_guard :
  'Auu____2632 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2632 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2632 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2632 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2669 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2669;
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
  'Auu____2680 .
    worklist ->
      'Auu____2680 FStar_TypeChecker_Common.problem ->
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
        let uu____2730 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2730
        then
          let uu____2731 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2732 = prob_to_string env d  in
          let uu____2733 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2731 uu____2732 uu____2733 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2739 -> failwith "impossible"  in
           let uu____2740 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2752 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2753 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2752, uu____2753)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2757 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2758 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2757, uu____2758)
              in
           match uu____2740 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___128_2776  ->
            match uu___128_2776 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2788 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___129_2810  ->
           match uu___129_2810 with
           | UNIV uu____2813 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2820 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2820
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
        (fun uu___130_2844  ->
           match uu___130_2844 with
           | UNIV (u',t) ->
               let uu____2849 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2849
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2853 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2864 =
        let uu____2865 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Primops;
          FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2865
         in
      FStar_Syntax_Subst.compress uu____2864
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2876 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Primops;
          FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2876
  
let norm_arg :
  'Auu____2883 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2883) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2883)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2906 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2906, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2947  ->
              match uu____2947 with
              | (x,imp) ->
                  let uu____2958 =
                    let uu___160_2959 = x  in
                    let uu____2960 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___160_2959.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___160_2959.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2960
                    }  in
                  (uu____2958, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2981 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2981
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2985 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2985
        | uu____2988 -> u2  in
      let uu____2989 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2989
  
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
                (let uu____3111 = norm_refinement env t12  in
                 match uu____3111 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3128;
                     FStar_Syntax_Syntax.vars = uu____3129;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3155 =
                       let uu____3156 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3157 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3156 uu____3157
                        in
                     failwith uu____3155)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3173 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3173
          | FStar_Syntax_Syntax.Tm_uinst uu____3174 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3211 =
                   let uu____3212 = FStar_Syntax_Subst.compress t1'  in
                   uu____3212.FStar_Syntax_Syntax.n  in
                 match uu____3211 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3229 -> aux true t1'
                 | uu____3236 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3251 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3282 =
                   let uu____3283 = FStar_Syntax_Subst.compress t1'  in
                   uu____3283.FStar_Syntax_Syntax.n  in
                 match uu____3282 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3300 -> aux true t1'
                 | uu____3307 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3322 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3367 =
                   let uu____3368 = FStar_Syntax_Subst.compress t1'  in
                   uu____3368.FStar_Syntax_Syntax.n  in
                 match uu____3367 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3385 -> aux true t1'
                 | uu____3392 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3407 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3422 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3437 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3452 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3467 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3494 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3525 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3546 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3575 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3602 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3639 ->
              let uu____3646 =
                let uu____3647 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3648 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3647 uu____3648
                 in
              failwith uu____3646
          | FStar_Syntax_Syntax.Tm_ascribed uu____3663 ->
              let uu____3690 =
                let uu____3691 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3692 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3691 uu____3692
                 in
              failwith uu____3690
          | FStar_Syntax_Syntax.Tm_delayed uu____3707 ->
              let uu____3732 =
                let uu____3733 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3734 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3733 uu____3734
                 in
              failwith uu____3732
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3749 =
                let uu____3750 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3751 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3750 uu____3751
                 in
              failwith uu____3749
           in
        let uu____3766 = whnf env t1  in aux false uu____3766
  
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
      let uu____3812 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3812 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3848 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3848, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3859 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3859 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3884 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3884 with
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
  fun uu____3967  ->
    match uu____3967 with
    | (t_base,refopt) ->
        let uu____4000 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4000 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4040 =
      let uu____4043 =
        let uu____4046 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4069  ->
                  match uu____4069 with | (uu____4076,uu____4077,x) -> x))
           in
        FStar_List.append wl.attempting uu____4046  in
      FStar_List.map (wl_prob_to_string wl) uu____4043  in
    FStar_All.pipe_right uu____4040 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4091 .
    ('Auu____4091,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4102  ->
    match uu____4102 with
    | (uu____4109,c,args) ->
        let uu____4112 = print_ctx_uvar c  in
        let uu____4113 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4112 uu____4113
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4119 = FStar_Syntax_Util.head_and_args t  in
    match uu____4119 with
    | (head1,_args) ->
        let uu____4156 =
          let uu____4157 = FStar_Syntax_Subst.compress head1  in
          uu____4157.FStar_Syntax_Syntax.n  in
        (match uu____4156 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4160 -> true
         | uu____4175 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4181 = FStar_Syntax_Util.head_and_args t  in
    match uu____4181 with
    | (head1,_args) ->
        let uu____4218 =
          let uu____4219 = FStar_Syntax_Subst.compress head1  in
          uu____4219.FStar_Syntax_Syntax.n  in
        (match uu____4218 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4223) -> u
         | uu____4244 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4267 = FStar_Syntax_Util.head_and_args t  in
      match uu____4267 with
      | (head1,args) ->
          let uu____4308 =
            let uu____4309 = FStar_Syntax_Subst.compress head1  in
            uu____4309.FStar_Syntax_Syntax.n  in
          (match uu____4308 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4317)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4360 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___131_4385  ->
                         match uu___131_4385 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4389 =
                               let uu____4390 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4390.FStar_Syntax_Syntax.n  in
                             (match uu____4389 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4394 -> false)
                         | uu____4395 -> true))
                  in
               (match uu____4360 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4417 =
                        FStar_List.collect
                          (fun uu___132_4423  ->
                             match uu___132_4423 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4427 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4427]
                             | uu____4428 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4417 FStar_List.rev  in
                    let uu____4437 =
                      let uu____4444 =
                        let uu____4451 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___133_4465  ->
                                  match uu___133_4465 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4469 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4469]
                                  | uu____4470 -> []))
                           in
                        FStar_All.pipe_right uu____4451 FStar_List.rev  in
                      let uu____4487 =
                        let uu____4490 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4490  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4444 uu____4487
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4437 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4519  ->
                                match uu____4519 with
                                | (x,i) ->
                                    let uu____4530 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4530, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4553  ->
                                match uu____4553 with
                                | (a,i) ->
                                    let uu____4564 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4564, i)) args_sol
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
           | uu____4580 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4600 =
          let uu____4613 =
            let uu____4614 = FStar_Syntax_Subst.compress k  in
            uu____4614.FStar_Syntax_Syntax.n  in
          match uu____4613 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4667 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4667)
              else
                (let uu____4681 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4681 with
                 | (ys',t1,uu____4704) ->
                     let uu____4709 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4709))
          | uu____4750 ->
              let uu____4751 =
                let uu____4762 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4762)  in
              ((ys, t), uu____4751)
           in
        match uu____4600 with
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
                 let uu____4811 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4811 c  in
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
               (let uu____4885 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4885
                then
                  let uu____4886 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4887 = print_ctx_uvar uv  in
                  let uu____4888 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4886 uu____4887 uu____4888
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
             let uu____4894 = p_guard_uvar prob  in
             match uu____4894 with
             | (xs,uv) ->
                 let fail1 uu____4906 =
                   let uu____4907 =
                     let uu____4908 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4909 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4908 uu____4909
                      in
                   failwith uu____4907  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____4959  ->
                           match uu____4959 with
                           | (a,i) ->
                               let uu____4972 =
                                 let uu____4973 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____4973.FStar_Syntax_Syntax.n  in
                               (match uu____4972 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____4991 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____4999 =
                     let uu____5000 = is_flex g  in
                     Prims.op_Negation uu____5000  in
                   if uu____4999
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____5004 = destruct_flex_t g wl  in
                      match uu____5004 with
                      | ((uu____5009,uv1,args),wl1) ->
                          ((let uu____5014 = args_as_binders args  in
                            assign_solution uu____5014 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___161_5016 = wl1  in
                   {
                     attempting = (uu___161_5016.attempting);
                     wl_deferred = (uu___161_5016.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___161_5016.defer_ok);
                     smt_ok = (uu___161_5016.smt_ok);
                     tcenv = (uu___161_5016.tcenv);
                     wl_implicits = (uu___161_5016.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5037 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5037
         then
           let uu____5038 = FStar_Util.string_of_int pid  in
           let uu____5039 =
             let uu____5040 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5040 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5038 uu____5039
         else ());
        commit sol;
        (let uu___162_5047 = wl  in
         {
           attempting = (uu___162_5047.attempting);
           wl_deferred = (uu___162_5047.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___162_5047.defer_ok);
           smt_ok = (uu___162_5047.smt_ok);
           tcenv = (uu___162_5047.tcenv);
           wl_implicits = (uu___162_5047.wl_implicits)
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
             | (uu____5109,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5135 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5135
              in
           (let uu____5141 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5141
            then
              let uu____5142 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5143 =
                let uu____5144 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5144 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5142 uu____5143
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
        let uu____5169 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5169 FStar_Util.set_elements  in
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
      let uu____5203 = occurs uk t  in
      match uu____5203 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5232 =
                 let uu____5233 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5234 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5233 uu____5234
                  in
               FStar_Pervasives_Native.Some uu____5232)
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
            let uu____5323 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5323 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5367 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5415  ->
             match uu____5415 with
             | (x,uu____5425) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5438 = FStar_List.last bs  in
      match uu____5438 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5456) ->
          let uu____5461 =
            FStar_Util.prefix_until
              (fun uu___134_5476  ->
                 match uu___134_5476 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5478 -> false) g
             in
          (match uu____5461 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5491,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5527 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5527 with
        | (pfx,uu____5537) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5549 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5549 with
             | (uu____5556,src',wl1) ->
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
                 | uu____5656 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5657 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5711  ->
                  fun uu____5712  ->
                    match (uu____5711, uu____5712) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5793 =
                          let uu____5794 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5794
                           in
                        if uu____5793
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5819 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5819
                           then
                             let uu____5832 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5832)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5657 with | (isect,uu____5869) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5898 'Auu____5899 .
    (FStar_Syntax_Syntax.bv,'Auu____5898) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5899) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5956  ->
              fun uu____5957  ->
                match (uu____5956, uu____5957) with
                | ((a,uu____5975),(b,uu____5977)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5992 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5992) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6022  ->
           match uu____6022 with
           | (y,uu____6028) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6039 'Auu____6040 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6039) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____6040)
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
                   let uu____6149 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6149
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____6157 =
                        let uu____6160 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____6160 :: seen  in
                      aux uu____6157 args2)
               | uu____6161 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6196 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6234 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6247 -> false
  
let string_of_option :
  'Auu____6254 .
    ('Auu____6254 -> Prims.string) ->
      'Auu____6254 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___135_6269  ->
      match uu___135_6269 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6275 = f x  in Prims.strcat "Some " uu____6275
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___136_6280  ->
    match uu___136_6280 with
    | MisMatch (d1,d2) ->
        let uu____6291 =
          let uu____6292 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6293 =
            let uu____6294 =
              let uu____6295 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6295 ")"  in
            Prims.strcat ") (" uu____6294  in
          Prims.strcat uu____6292 uu____6293  in
        Prims.strcat "MisMatch (" uu____6291
    | HeadMatch u ->
        let uu____6297 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6297
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___137_6302  ->
    match uu___137_6302 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6317 -> HeadMatch false
  
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
          let uu____6331 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6331 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6342 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6365 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6374 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6402 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6402
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6403 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6404 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6405 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6420 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6433 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6457) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6463,uu____6464) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6506) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6527;
             FStar_Syntax_Syntax.index = uu____6528;
             FStar_Syntax_Syntax.sort = t2;_},uu____6530)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6537 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6538 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6539 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6552 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6559 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6577 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6577
  
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
            let uu____6604 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6604
            then FullMatch
            else
              (let uu____6606 =
                 let uu____6615 =
                   let uu____6618 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6618  in
                 let uu____6619 =
                   let uu____6622 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6622  in
                 (uu____6615, uu____6619)  in
               MisMatch uu____6606)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6628),FStar_Syntax_Syntax.Tm_uinst (g,uu____6630)) ->
            let uu____6639 = head_matches env f g  in
            FStar_All.pipe_right uu____6639 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6642 = FStar_Const.eq_const c d  in
            if uu____6642
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6649),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6651)) ->
            let uu____6692 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6692
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6699),FStar_Syntax_Syntax.Tm_refine (y,uu____6701)) ->
            let uu____6710 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6710 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6712),uu____6713) ->
            let uu____6718 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6718 head_match
        | (uu____6719,FStar_Syntax_Syntax.Tm_refine (x,uu____6721)) ->
            let uu____6726 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6726 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6727,FStar_Syntax_Syntax.Tm_type
           uu____6728) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6729,FStar_Syntax_Syntax.Tm_arrow uu____6730) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6756),FStar_Syntax_Syntax.Tm_app (head',uu____6758))
            ->
            let uu____6799 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6799 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6801),uu____6802) ->
            let uu____6823 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6823 head_match
        | (uu____6824,FStar_Syntax_Syntax.Tm_app (head1,uu____6826)) ->
            let uu____6847 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6847 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6848,FStar_Syntax_Syntax.Tm_let
           uu____6849) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6874,FStar_Syntax_Syntax.Tm_match uu____6875) ->
            HeadMatch true
        | uu____6920 ->
            let uu____6925 =
              let uu____6934 = delta_depth_of_term env t11  in
              let uu____6937 = delta_depth_of_term env t21  in
              (uu____6934, uu____6937)  in
            MisMatch uu____6925
  
let head_matches_delta :
  'Auu____6954 .
    FStar_TypeChecker_Env.env ->
      'Auu____6954 ->
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
            (let uu____7003 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7003
             then
               let uu____7004 = FStar_Syntax_Print.term_to_string t  in
               let uu____7005 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7004 uu____7005
             else ());
            (let uu____7007 =
               let uu____7008 = FStar_Syntax_Util.un_uinst head1  in
               uu____7008.FStar_Syntax_Syntax.n  in
             match uu____7007 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7014 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7014 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7028 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7028
                        then
                          let uu____7029 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7029
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7031 ->
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
                      ((let uu____7042 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7042
                        then
                          let uu____7043 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7044 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7043
                            uu____7044
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7046 -> FStar_Pervasives_Native.None)
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
            (let uu____7184 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7184
             then
               let uu____7185 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7186 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7187 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7185
                 uu____7186 uu____7187
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7211 =
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
               match uu____7211 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7256 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7256 with
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
                  uu____7288),uu____7289)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7307 =
                      let uu____7316 = maybe_inline t11  in
                      let uu____7319 = maybe_inline t21  in
                      (uu____7316, uu____7319)  in
                    match uu____7307 with
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
                 (uu____7356,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7357))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7375 =
                      let uu____7384 = maybe_inline t11  in
                      let uu____7387 = maybe_inline t21  in
                      (uu____7384, uu____7387)  in
                    match uu____7375 with
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
             | MisMatch uu____7436 -> fail1 n_delta r t11 t21
             | uu____7445 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7458 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7458
           then
             let uu____7459 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7460 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7461 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7468 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7486 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7486
                    (fun uu____7520  ->
                       match uu____7520 with
                       | (t11,t21) ->
                           let uu____7527 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7528 =
                             let uu____7529 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7529  in
                           Prims.strcat uu____7527 uu____7528))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7459 uu____7460 uu____7461 uu____7468
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7541 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7541 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___138_7554  ->
    match uu___138_7554 with
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
      let uu___163_7591 = p  in
      let uu____7594 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7595 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___163_7591.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7594;
        FStar_TypeChecker_Common.relation =
          (uu___163_7591.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7595;
        FStar_TypeChecker_Common.element =
          (uu___163_7591.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___163_7591.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___163_7591.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___163_7591.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___163_7591.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___163_7591.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7609 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7609
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7614 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7636 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7636 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7644 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7644 with
           | (lh,lhs_args) ->
               let uu____7685 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7685 with
                | (rh,rhs_args) ->
                    let uu____7726 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7739,FStar_Syntax_Syntax.Tm_uvar uu____7740)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7821 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7844,uu____7845)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_7863 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_7863.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_7863.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_7863.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_7863.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_7863.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_7863.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_7863.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_7863.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_7863.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7866,FStar_Syntax_Syntax.Tm_uvar uu____7867)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___164_7885 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___164_7885.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___164_7885.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___164_7885.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___164_7885.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___164_7885.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___164_7885.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___164_7885.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___164_7885.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___164_7885.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7888,FStar_Syntax_Syntax.Tm_arrow uu____7889)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___165_7919 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___165_7919.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___165_7919.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___165_7919.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___165_7919.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___165_7919.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___165_7919.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___165_7919.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___165_7919.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___165_7919.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7922,FStar_Syntax_Syntax.Tm_type uu____7923)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___165_7941 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___165_7941.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___165_7941.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___165_7941.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___165_7941.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___165_7941.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___165_7941.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___165_7941.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___165_7941.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___165_7941.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7944,FStar_Syntax_Syntax.Tm_uvar uu____7945)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___165_7963 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___165_7963.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___165_7963.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___165_7963.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___165_7963.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___165_7963.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___165_7963.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___165_7963.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___165_7963.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___165_7963.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7966,FStar_Syntax_Syntax.Tm_uvar uu____7967)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7984,uu____7985)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8002,FStar_Syntax_Syntax.Tm_uvar uu____8003)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8020,uu____8021) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7726 with
                     | (rank,tp1) ->
                         let uu____8034 =
                           FStar_All.pipe_right
                             (let uu___166_8038 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___166_8038.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___166_8038.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___166_8038.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___166_8038.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___166_8038.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___166_8038.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___166_8038.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___166_8038.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___166_8038.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8034))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8044 =
            FStar_All.pipe_right
              (let uu___167_8048 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___167_8048.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___167_8048.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___167_8048.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___167_8048.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___167_8048.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___167_8048.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___167_8048.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___167_8048.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___167_8048.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8044)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8109 probs =
      match uu____8109 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8190 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8211 = rank wl.tcenv hd1  in
               (match uu____8211 with
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
                      (let uu____8270 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8274 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8274)
                          in
                       if uu____8270
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
          let uu____8342 = FStar_Syntax_Util.head_and_args t  in
          match uu____8342 with
          | (hd1,uu____8358) ->
              let uu____8379 =
                let uu____8380 = FStar_Syntax_Subst.compress hd1  in
                uu____8380.FStar_Syntax_Syntax.n  in
              (match uu____8379 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8384) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8418  ->
                           match uu____8418 with
                           | (y,uu____8424) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8438  ->
                                       match uu____8438 with
                                       | (x,uu____8444) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8445 -> false)
           in
        let uu____8446 = rank tcenv p  in
        match uu____8446 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8453 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8480 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8494 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8508 -> false
  
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
                        let uu____8560 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8560 with
                        | (k,uu____8566) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8576 -> false)))
            | uu____8577 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8629 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8635 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8635 = (Prims.parse_int "0")))
                           in
                        if uu____8629 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8651 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8657 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8657 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8651)
               in
            let uu____8658 = filter1 u12  in
            let uu____8661 = filter1 u22  in (uu____8658, uu____8661)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8690 = filter_out_common_univs us1 us2  in
                (match uu____8690 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8749 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8749 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8752 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8762 =
                          let uu____8763 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8764 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8763
                            uu____8764
                           in
                        UFailed uu____8762))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8788 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8788 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8814 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8814 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8817 ->
                let uu____8822 =
                  let uu____8823 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8824 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8823
                    uu____8824 msg
                   in
                UFailed uu____8822
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8825,uu____8826) ->
              let uu____8827 =
                let uu____8828 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8829 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8828 uu____8829
                 in
              failwith uu____8827
          | (FStar_Syntax_Syntax.U_unknown ,uu____8830) ->
              let uu____8831 =
                let uu____8832 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8833 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8832 uu____8833
                 in
              failwith uu____8831
          | (uu____8834,FStar_Syntax_Syntax.U_bvar uu____8835) ->
              let uu____8836 =
                let uu____8837 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8838 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8837 uu____8838
                 in
              failwith uu____8836
          | (uu____8839,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8840 =
                let uu____8841 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8842 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8841 uu____8842
                 in
              failwith uu____8840
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8866 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8866
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8880 = occurs_univ v1 u3  in
              if uu____8880
              then
                let uu____8881 =
                  let uu____8882 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8883 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8882 uu____8883
                   in
                try_umax_components u11 u21 uu____8881
              else
                (let uu____8885 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8885)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8897 = occurs_univ v1 u3  in
              if uu____8897
              then
                let uu____8898 =
                  let uu____8899 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8900 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8899 uu____8900
                   in
                try_umax_components u11 u21 uu____8898
              else
                (let uu____8902 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8902)
          | (FStar_Syntax_Syntax.U_max uu____8903,uu____8904) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8910 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8910
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8912,FStar_Syntax_Syntax.U_max uu____8913) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8919 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8919
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8921,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8922,FStar_Syntax_Syntax.U_name
             uu____8923) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8924) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8925) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8926,FStar_Syntax_Syntax.U_succ
             uu____8927) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8928,FStar_Syntax_Syntax.U_zero
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
      let uu____9028 = bc1  in
      match uu____9028 with
      | (bs1,mk_cod1) ->
          let uu____9072 = bc2  in
          (match uu____9072 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9183 = aux xs ys  in
                     (match uu____9183 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9266 =
                       let uu____9273 = mk_cod1 xs  in ([], uu____9273)  in
                     let uu____9276 =
                       let uu____9283 = mk_cod2 ys  in ([], uu____9283)  in
                     (uu____9266, uu____9276)
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
                  let uu____9353 =
                    let uu____9354 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9354 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9353
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9359 = has_type_guard t1 t2  in (uu____9359, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9360 = has_type_guard t2 t1  in (uu____9360, wl)
  
let is_flex_pat :
  'Auu____9369 'Auu____9370 'Auu____9371 .
    ('Auu____9369,'Auu____9370,'Auu____9371 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___139_9384  ->
    match uu___139_9384 with
    | (uu____9393,uu____9394,[]) -> true
    | uu____9397 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9428 = f  in
      match uu____9428 with
      | (uu____9435,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9436;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9437;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9440;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9441;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9442;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9494  ->
                 match uu____9494 with
                 | (y,uu____9500) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9622 =
                  let uu____9635 =
                    let uu____9638 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9638  in
                  ((FStar_List.rev pat_binders), uu____9635)  in
                FStar_Pervasives_Native.Some uu____9622
            | (uu____9665,[]) ->
                let uu____9688 =
                  let uu____9701 =
                    let uu____9704 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9704  in
                  ((FStar_List.rev pat_binders), uu____9701)  in
                FStar_Pervasives_Native.Some uu____9688
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9769 =
                  let uu____9770 = FStar_Syntax_Subst.compress a  in
                  uu____9770.FStar_Syntax_Syntax.n  in
                (match uu____9769 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9788 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9788
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___168_9809 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___168_9809.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___168_9809.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9813 =
                            let uu____9814 =
                              let uu____9821 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9821)  in
                            FStar_Syntax_Syntax.NT uu____9814  in
                          [uu____9813]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___169_9833 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___169_9833.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___169_9833.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9834 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9862 =
                  let uu____9875 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9875  in
                (match uu____9862 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9938 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9965 ->
               let uu____9966 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9966 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10242 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10242
       then
         let uu____10243 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10243
       else ());
      (let uu____10245 = next_prob probs  in
       match uu____10245 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___170_10272 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___170_10272.wl_deferred);
               ctr = (uu___170_10272.ctr);
               defer_ok = (uu___170_10272.defer_ok);
               smt_ok = (uu___170_10272.smt_ok);
               tcenv = (uu___170_10272.tcenv);
               wl_implicits = (uu___170_10272.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____10279 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____10279
                then
                  let uu____10280 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____10280
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
                          (let uu___171_10285 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___171_10285.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___171_10285.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___171_10285.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___171_10285.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___171_10285.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___171_10285.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___171_10285.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___171_10285.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___171_10285.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10307 ->
                let uu____10316 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10375  ->
                          match uu____10375 with
                          | (c,uu____10383,uu____10384) -> c < probs.ctr))
                   in
                (match uu____10316 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10425 =
                            let uu____10430 =
                              FStar_List.map
                                (fun uu____10445  ->
                                   match uu____10445 with
                                   | (uu____10456,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10430, (probs.wl_implicits))  in
                          Success uu____10425
                      | uu____10459 ->
                          let uu____10468 =
                            let uu___172_10469 = probs  in
                            let uu____10470 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10489  ->
                                      match uu____10489 with
                                      | (uu____10496,uu____10497,y) -> y))
                               in
                            {
                              attempting = uu____10470;
                              wl_deferred = rest;
                              ctr = (uu___172_10469.ctr);
                              defer_ok = (uu___172_10469.defer_ok);
                              smt_ok = (uu___172_10469.smt_ok);
                              tcenv = (uu___172_10469.tcenv);
                              wl_implicits = (uu___172_10469.wl_implicits)
                            }  in
                          solve env uu____10468))))

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
            let uu____10504 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10504 with
            | USolved wl1 ->
                let uu____10506 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10506
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
                  let uu____10558 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10558 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10561 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10573;
                  FStar_Syntax_Syntax.vars = uu____10574;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10577;
                  FStar_Syntax_Syntax.vars = uu____10578;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10590,uu____10591) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10598,FStar_Syntax_Syntax.Tm_uinst uu____10599) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10606 -> USolved wl

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
            ((let uu____10616 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10616
              then
                let uu____10617 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10617 msg
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
              let uu____10702 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10702 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10754 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10754
               then
                 let uu____10755 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10756 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10755
                   uu____10756
               else ());
              (let uu____10758 = head_matches_delta env1 () t1 t2  in
               match uu____10758 with
               | (mr,ts1) ->
                   (match mr with
                    | HeadMatch (true ) ->
                        let uu____10803 = eq_prob t1 t2 wl2  in
                        (match uu____10803 with | (p,wl3) -> (t1, [p], wl3))
                    | MisMatch uu____10824 ->
                        let uu____10833 = eq_prob t1 t2 wl2  in
                        (match uu____10833 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch (false ) ->
                        let uu____10880 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10895 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10896 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10895, uu____10896)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10901 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10902 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10901, uu____10902)
                           in
                        (match uu____10880 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10933 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10933 with
                               | (t1_hd,t1_args) ->
                                   let uu____10972 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10972 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____11026 =
                                             let uu____11033 =
                                               let uu____11042 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____11042 :: t1_args  in
                                             let uu____11055 =
                                               let uu____11062 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____11062 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____11103  ->
                                                  fun uu____11104  ->
                                                    fun uu____11105  ->
                                                      match (uu____11103,
                                                              uu____11104,
                                                              uu____11105)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____11147),
                                                         (a2,uu____11149)) ->
                                                          let uu____11174 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____11174
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____11033
                                               uu____11055
                                              in
                                           match uu____11026 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___173_11200 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___173_11200.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___173_11200.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11218 =
                                                 solve env1 wl'  in
                                               (match uu____11218 with
                                                | Success (uu____11221,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___174_11225 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___174_11225.attempting);
                                                           wl_deferred =
                                                             (uu___174_11225.wl_deferred);
                                                           ctr =
                                                             (uu___174_11225.ctr);
                                                           defer_ok =
                                                             (uu___174_11225.defer_ok);
                                                           smt_ok =
                                                             (uu___174_11225.smt_ok);
                                                           tcenv =
                                                             (uu___174_11225.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____11236 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____11268 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____11268 with
                               | (t1_base,p1_opt) ->
                                   let uu____11315 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____11315 with
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
                                              let uu____11452 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____11452
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
                                              let uu____11482 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11482
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
                                              let uu____11512 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____11512
                                          | uu____11515 -> t_base  in
                                        let uu____11532 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11532 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11546 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11546, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11553 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11553 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11600 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11600 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11647 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11647
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
                             let uu____11671 = combine t11 t21 wl2  in
                             (match uu____11671 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11704 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11704
                                    then
                                      let uu____11705 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11705
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11744 ts1 =
              match uu____11744 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11807 = pairwise out t wl2  in
                       (match uu____11807 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11843 =
              let uu____11854 = FStar_List.hd ts  in (uu____11854, [], wl1)
               in
            let uu____11863 = FStar_List.tl ts  in
            aux uu____11843 uu____11863  in
          let uu____11870 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11870 with
          | (this_flex,this_rigid) ->
              let uu____11882 =
                let uu____11883 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11883.FStar_Syntax_Syntax.n  in
              (match uu____11882 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11904 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11904
                   then
                     let uu____11905 = destruct_flex_t this_flex wl  in
                     (match uu____11905 with
                      | (flex,wl1) ->
                          let uu____11912 = quasi_pattern env flex  in
                          (match uu____11912 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11930 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11930
                                 then
                                   let uu____11931 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11931
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
                             ((let uu___175_11936 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___175_11936.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___175_11936.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___175_11936.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___175_11936.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___175_11936.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___175_11936.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___175_11936.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___175_11936.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___175_11936.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11937 ->
                   ((let uu____11939 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11939
                     then
                       let uu____11940 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11940
                     else ());
                    (let uu____11942 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11942 with
                     | (u,_args) ->
                         let uu____11979 =
                           let uu____11980 = FStar_Syntax_Subst.compress u
                              in
                           uu____11980.FStar_Syntax_Syntax.n  in
                         (match uu____11979 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____12011 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____12011 with
                                | (u',uu____12027) ->
                                    let uu____12048 =
                                      let uu____12049 = whnf env u'  in
                                      uu____12049.FStar_Syntax_Syntax.n  in
                                    (match uu____12048 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____12074 -> false)
                                 in
                              let uu____12075 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___140_12098  ->
                                        match uu___140_12098 with
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
                                             | uu____12107 -> false)
                                        | uu____12110 -> false))
                                 in
                              (match uu____12075 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____12124 = whnf env this_rigid
                                        in
                                     let uu____12125 =
                                       FStar_List.collect
                                         (fun uu___141_12131  ->
                                            match uu___141_12131 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____12137 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____12137]
                                            | uu____12139 -> []) bounds_probs
                                        in
                                     uu____12124 :: uu____12125  in
                                   let uu____12140 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____12140 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____12171 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____12186 =
                                              let uu____12187 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____12187.FStar_Syntax_Syntax.n
                                               in
                                            match uu____12186 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____12199 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____12199)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____12208 -> bound  in
                                          let uu____12209 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____12209)  in
                                        (match uu____12171 with
                                         | (bound_typ,(eq_prob,wl2)) ->
                                             ((let uu____12237 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____12237
                                               then
                                                 let wl' =
                                                   let uu___176_12239 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___176_12239.wl_deferred);
                                                     ctr =
                                                       (uu___176_12239.ctr);
                                                     defer_ok =
                                                       (uu___176_12239.defer_ok);
                                                     smt_ok =
                                                       (uu___176_12239.smt_ok);
                                                     tcenv =
                                                       (uu___176_12239.tcenv);
                                                     wl_implicits =
                                                       (uu___176_12239.wl_implicits)
                                                   }  in
                                                 let uu____12240 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____12240
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____12243 =
                                                 solve_t env eq_prob
                                                   (let uu___177_12245 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___177_12245.wl_deferred);
                                                      ctr =
                                                        (uu___177_12245.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___177_12245.smt_ok);
                                                      tcenv =
                                                        (uu___177_12245.tcenv);
                                                      wl_implicits =
                                                        (uu___177_12245.wl_implicits)
                                                    })
                                                  in
                                               match uu____12243 with
                                               | Success uu____12246 ->
                                                   let wl3 =
                                                     let uu___178_12252 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___178_12252.wl_deferred);
                                                       ctr =
                                                         (uu___178_12252.ctr);
                                                       defer_ok =
                                                         (uu___178_12252.defer_ok);
                                                       smt_ok =
                                                         (uu___178_12252.smt_ok);
                                                       tcenv =
                                                         (uu___178_12252.tcenv);
                                                       wl_implicits =
                                                         (uu___178_12252.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____12256 =
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
                                                    (let uu____12268 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____12268
                                                     then
                                                       let uu____12269 =
                                                         let uu____12270 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____12270
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____12269
                                                     else ());
                                                    (let uu____12276 =
                                                       let uu____12291 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____12291)
                                                        in
                                                     match uu____12276 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____12313))
                                                         ->
                                                         let uu____12338 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12338
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
                                                         let uu____12377 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____12377
                                                          with
                                                          | (eq_prob1,wl3) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl3 tp x
                                                                  phi
                                                                 in
                                                              let wl4 =
                                                                let uu____12394
                                                                  =
                                                                  let uu____12399
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12399
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____12394
                                                                  [] wl3
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl4))
                                                     | uu____12404 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____12419 when flip ->
                              let uu____12420 =
                                let uu____12421 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12422 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a flex-rigid: %s"
                                  uu____12421 uu____12422
                                 in
                              failwith uu____12420
                          | uu____12423 ->
                              let uu____12424 =
                                let uu____12425 =
                                  FStar_Util.string_of_int (rank_t_num rank1)
                                   in
                                let uu____12426 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format2
                                  "Impossible: (rank=%s) Not a rigid-flex: %s"
                                  uu____12425 uu____12426
                                 in
                              failwith uu____12424))))

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
                      (fun uu____12454  ->
                         match uu____12454 with
                         | (x,i) ->
                             let uu____12465 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12465, i)) bs_lhs
                     in
                  let uu____12466 = lhs  in
                  match uu____12466 with
                  | (uu____12467,u_lhs,uu____12469) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12582 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12592 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12592, univ)
                             in
                          match uu____12582 with
                          | (k,univ) ->
                              let uu____12605 =
                                let uu____12612 =
                                  let uu____12615 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12615
                                   in
                                copy_uvar u_lhs uu____12612 wl2  in
                              (match uu____12605 with
                               | (uu____12628,u,wl3) ->
                                   let uu____12631 =
                                     let uu____12634 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12634
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12631, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12670 =
                              let uu____12683 =
                                let uu____12692 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12692 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12738  ->
                                   fun uu____12739  ->
                                     match (uu____12738, uu____12739) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12830 =
                                           let uu____12837 =
                                             let uu____12840 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12840
                                              in
                                           copy_uvar u_lhs uu____12837 wl2
                                            in
                                         (match uu____12830 with
                                          | (uu____12863,t_a,wl3) ->
                                              let uu____12866 =
                                                let uu____12873 =
                                                  let uu____12876 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12876
                                                   in
                                                copy_uvar u_lhs uu____12873
                                                  wl3
                                                 in
                                              (match uu____12866 with
                                               | (uu____12891,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12683
                                ([], wl1)
                               in
                            (match uu____12670 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___179_12952 = ct  in
                                   let uu____12953 =
                                     let uu____12956 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12956
                                      in
                                   let uu____12971 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___179_12952.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___179_12952.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12953;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12971;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___179_12952.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___180_12989 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___180_12989.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___180_12989.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12992 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12992 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13046 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13046 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13063 =
                                          let uu____13068 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13068)  in
                                        TERM uu____13063  in
                                      let uu____13069 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13069 with
                                       | (sub_prob,wl3) ->
                                           let uu____13080 =
                                             let uu____13081 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13081
                                              in
                                           solve env uu____13080))
                             | (x,imp)::formals2 ->
                                 let uu____13095 =
                                   let uu____13102 =
                                     let uu____13105 =
                                       let uu____13108 =
                                         let uu____13109 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____13109
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____13108
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____13105
                                      in
                                   copy_uvar u_lhs uu____13102 wl1  in
                                 (match uu____13095 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____13133 =
                                          let uu____13136 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13136
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13133 t_y
                                         in
                                      let uu____13137 =
                                        let uu____13140 =
                                          let uu____13143 =
                                            let uu____13144 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13144, imp)  in
                                          [uu____13143]  in
                                        FStar_List.append bs_terms
                                          uu____13140
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13137 formals2 wl2)
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
              (let uu____13186 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13186
               then
                 let uu____13187 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13188 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13187 (rel_to_string (p_rel orig)) uu____13188
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13293 = rhs wl1 scope env1 subst1  in
                     (match uu____13293 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13313 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13313
                            then
                              let uu____13314 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13314
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___181_13368 = hd1  in
                       let uu____13369 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___181_13368.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___181_13368.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13369
                       }  in
                     let hd21 =
                       let uu___182_13373 = hd2  in
                       let uu____13374 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___182_13373.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___182_13373.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13374
                       }  in
                     let uu____13377 =
                       let uu____13382 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13382
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13377 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13401 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13401
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13405 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13405 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13460 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13460
                                  in
                               ((let uu____13472 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13472
                                 then
                                   let uu____13473 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13474 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13473
                                     uu____13474
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13501 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13530 = aux wl [] env [] bs1 bs2  in
               match uu____13530 with
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
        (let uu____13581 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13581 wl)

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
              let uu____13595 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13595 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13625 = lhs1  in
              match uu____13625 with
              | (uu____13628,ctx_u,uu____13630) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13636 ->
                        let uu____13637 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13637 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13684 = quasi_pattern env1 lhs1  in
              match uu____13684 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13714) ->
                  let uu____13719 = lhs1  in
                  (match uu____13719 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13733 = occurs_check ctx_u rhs1  in
                       (match uu____13733 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13775 =
                                let uu____13782 =
                                  let uu____13783 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13783
                                   in
                                FStar_Util.Inl uu____13782  in
                              (uu____13775, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13803 =
                                 let uu____13804 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13804  in
                               if uu____13803
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13824 =
                                    let uu____13831 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13831  in
                                  let uu____13836 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13824, uu____13836)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13898  ->
                     match uu____13898 with
                     | (x,i) ->
                         let uu____13909 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13909, i)) bs_lhs
                 in
              let uu____13910 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13910 with
              | (rhs_hd,args) ->
                  let uu____13947 = FStar_Util.prefix args  in
                  (match uu____13947 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14005 = lhs1  in
                       (match uu____14005 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14009 =
                              let uu____14020 =
                                let uu____14027 =
                                  let uu____14030 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14030
                                   in
                                copy_uvar u_lhs uu____14027 wl1  in
                              match uu____14020 with
                              | (uu____14051,t_last_arg,wl2) ->
                                  let uu____14054 =
                                    let uu____14061 =
                                      let uu____14064 =
                                        let uu____14071 =
                                          let uu____14078 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____14078]  in
                                        FStar_List.append bs_lhs uu____14071
                                         in
                                      let uu____14095 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____14064
                                        uu____14095
                                       in
                                    copy_uvar u_lhs uu____14061 wl2  in
                                  (match uu____14054 with
                                   | (uu____14108,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14114 =
                                         let uu____14121 =
                                           let uu____14124 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____14124
                                            in
                                         copy_uvar u_lhs uu____14121 wl3  in
                                       (match uu____14114 with
                                        | (uu____14137,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14009 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14161 =
                                     let uu____14162 =
                                       let uu____14167 =
                                         let uu____14168 =
                                           let uu____14171 =
                                             let uu____14176 =
                                               let uu____14177 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14177]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14176
                                              in
                                           uu____14171
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14168
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14167)  in
                                     TERM uu____14162  in
                                   [uu____14161]  in
                                 let uu____14198 =
                                   let uu____14205 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14205 with
                                   | (p1,wl3) ->
                                       let uu____14222 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14222 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14198 with
                                  | (sub_probs,wl3) ->
                                      let uu____14249 =
                                        let uu____14250 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14250  in
                                      solve env1 uu____14249))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14283 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14283 with
                | (uu____14298,args) ->
                    (match args with | [] -> false | uu____14326 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14341 =
                  let uu____14342 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14342.FStar_Syntax_Syntax.n  in
                match uu____14341 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14345 -> true
                | uu____14358 -> false  in
              let uu____14359 = quasi_pattern env1 lhs1  in
              match uu____14359 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14370 =
                    let uu____14371 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14371
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14370
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14378 = is_app rhs1  in
                  if uu____14378
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14380 = is_arrow rhs1  in
                     if uu____14380
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14382 =
                          let uu____14383 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14383
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14382))
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
                let uu____14386 = lhs  in
                (match uu____14386 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14390 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14390 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14405 =
                              let uu____14408 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14408
                               in
                            FStar_All.pipe_right uu____14405
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14423 = occurs_check ctx_uv rhs1  in
                          (match uu____14423 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14445 =
                                   let uu____14446 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14446
                                    in
                                 giveup_or_defer env orig wl uu____14445
                               else
                                 (let uu____14448 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14448
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14453 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14453
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14455 =
                                         let uu____14456 =
                                           names_to_string1 fvs2  in
                                         let uu____14457 =
                                           names_to_string1 fvs1  in
                                         let uu____14458 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14456 uu____14457
                                           uu____14458
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14455)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14464 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14468 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14468 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14491 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14491
                             | (FStar_Util.Inl msg,uu____14493) ->
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
                  (let uu____14522 =
                     let uu____14539 = quasi_pattern env lhs  in
                     let uu____14546 = quasi_pattern env rhs  in
                     (uu____14539, uu____14546)  in
                   match uu____14522 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14589 = lhs  in
                       (match uu____14589 with
                        | ({ FStar_Syntax_Syntax.n = uu____14590;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14592;_},u_lhs,uu____14594)
                            ->
                            let uu____14597 = rhs  in
                            (match uu____14597 with
                             | (uu____14598,u_rhs,uu____14600) ->
                                 let uu____14601 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14601
                                 then
                                   let uu____14602 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14602
                                 else
                                   (let uu____14604 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14604 with
                                    | (sub_prob,wl1) ->
                                        let uu____14615 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14615 with
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
                                             let uu____14643 =
                                               let uu____14650 =
                                                 let uu____14653 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14653
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
                                                 uu____14650
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____14643 with
                                              | (uu____14656,w,wl2) ->
                                                  let w_app =
                                                    let uu____14662 =
                                                      let uu____14667 =
                                                        FStar_List.map
                                                          (fun uu____14676 
                                                             ->
                                                             match uu____14676
                                                             with
                                                             | (z,uu____14682)
                                                                 ->
                                                                 let uu____14683
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14683)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14667
                                                       in
                                                    uu____14662
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14687 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14687
                                                    then
                                                      let uu____14688 =
                                                        let uu____14691 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14692 =
                                                          let uu____14695 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14696 =
                                                            let uu____14699 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14700 =
                                                              let uu____14703
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14708
                                                                =
                                                                let uu____14711
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14716
                                                                  =
                                                                  let uu____14719
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14719]
                                                                   in
                                                                uu____14711
                                                                  ::
                                                                  uu____14716
                                                                 in
                                                              uu____14703 ::
                                                                uu____14708
                                                               in
                                                            uu____14699 ::
                                                              uu____14700
                                                             in
                                                          uu____14695 ::
                                                            uu____14696
                                                           in
                                                        uu____14691 ::
                                                          uu____14692
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14688
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14725 =
                                                          let uu____14730 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14730)
                                                           in
                                                        TERM uu____14725  in
                                                      let uu____14731 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14731
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14736 =
                                                             let uu____14741
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
                                                               uu____14741)
                                                              in
                                                           TERM uu____14736
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14742 =
                                                      let uu____14743 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14743
                                                       in
                                                    solve env uu____14742)))))))
                   | uu____14744 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14808 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14808
            then
              let uu____14809 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14810 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14811 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14812 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14809 uu____14810 uu____14811 uu____14812
            else ());
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
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14817 uu____14818 uu____14819 uu____14820
            else ());
           (let uu____14822 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14822 with
            | (head1,args1) ->
                let uu____14859 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14859 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____14913 =
                         let uu____14914 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14915 = args_to_string args1  in
                         let uu____14916 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____14917 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____14914 uu____14915 uu____14916 uu____14917
                          in
                       giveup env1 uu____14913 orig
                     else
                       (let uu____14919 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____14926 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____14926 = FStar_Syntax_Util.Equal)
                           in
                        if uu____14919
                        then
                          let uu____14927 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____14927 with
                          | USolved wl2 ->
                              let uu____14929 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____14929
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____14933 = base_and_refinement env1 t1  in
                           match uu____14933 with
                           | (base1,refinement1) ->
                               let uu____14958 = base_and_refinement env1 t2
                                  in
                               (match uu____14958 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15015 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15015 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15019 =
                                                FStar_List.fold_right2
                                                  (fun uu____15052  ->
                                                     fun uu____15053  ->
                                                       fun uu____15054  ->
                                                         match (uu____15052,
                                                                 uu____15053,
                                                                 uu____15054)
                                                         with
                                                         | ((a,uu____15090),
                                                            (a',uu____15092),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15113
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15113
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15019 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15141 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15141
                                                     then
                                                       let uu____15142 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15142
                                                     else ());
                                                    (let formula =
                                                       let uu____15147 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15147
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     solve env1
                                                       (attempt subprobs wl4)))))
                                     | uu____15155 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___183_15195 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___183_15195.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___183_15195.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___183_15195.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___183_15195.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___183_15195.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___183_15195.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___183_15195.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___183_15195.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15233 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15233
            then
              let uu____15234 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15235 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15236 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15237 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15234 uu____15235 uu____15236 uu____15237
            else ());
           (let uu____15239 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15239 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15270,uu____15271) ->
                     let rec may_relate head3 =
                       let uu____15298 =
                         let uu____15299 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15299.FStar_Syntax_Syntax.n  in
                       match uu____15298 with
                       | FStar_Syntax_Syntax.Tm_name uu____15302 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15303 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15326;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15327;
                             FStar_Syntax_Syntax.fv_qual = uu____15328;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15331;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15332;
                             FStar_Syntax_Syntax.fv_qual = uu____15333;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15337,uu____15338) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15380) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15386) ->
                           may_relate t
                       | uu____15391 -> false  in
                     let uu____15392 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15392
                     then
                       let uu____15393 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15393 with
                        | (guard,wl2) ->
                            let uu____15400 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15400)
                     else
                       (let uu____15402 =
                          let uu____15403 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15404 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15403 uu____15404
                           in
                        giveup env1 uu____15402 orig)
                 | (uu____15405,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___184_15419 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___184_15419.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___184_15419.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___184_15419.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___184_15419.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___184_15419.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___184_15419.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___184_15419.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___184_15419.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15443 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15443
          then
            let uu____15444 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15444
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15449 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15449
              then
                let uu____15450 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15451 =
                  let uu____15452 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15453 =
                    let uu____15454 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15454  in
                  Prims.strcat uu____15452 uu____15453  in
                let uu____15455 =
                  let uu____15456 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15457 =
                    let uu____15458 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15458  in
                  Prims.strcat uu____15456 uu____15457  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15450
                  uu____15451 uu____15455
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15461,uu____15462) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15487,FStar_Syntax_Syntax.Tm_delayed uu____15488) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15513,uu____15514) ->
                  let uu____15541 =
                    let uu___185_15542 = problem  in
                    let uu____15543 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___185_15542.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15543;
                      FStar_TypeChecker_Common.relation =
                        (uu___185_15542.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___185_15542.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___185_15542.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___185_15542.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___185_15542.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___185_15542.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___185_15542.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___185_15542.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15541 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15544,uu____15545) ->
                  let uu____15552 =
                    let uu___186_15553 = problem  in
                    let uu____15554 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___186_15553.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15554;
                      FStar_TypeChecker_Common.relation =
                        (uu___186_15553.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___186_15553.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___186_15553.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___186_15553.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___186_15553.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___186_15553.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___186_15553.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___186_15553.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15552 wl
              | (uu____15555,FStar_Syntax_Syntax.Tm_ascribed uu____15556) ->
                  let uu____15583 =
                    let uu___187_15584 = problem  in
                    let uu____15585 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___187_15584.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___187_15584.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___187_15584.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15585;
                      FStar_TypeChecker_Common.element =
                        (uu___187_15584.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___187_15584.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___187_15584.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___187_15584.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___187_15584.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___187_15584.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15583 wl
              | (uu____15586,FStar_Syntax_Syntax.Tm_meta uu____15587) ->
                  let uu____15594 =
                    let uu___188_15595 = problem  in
                    let uu____15596 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___188_15595.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___188_15595.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___188_15595.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15596;
                      FStar_TypeChecker_Common.element =
                        (uu___188_15595.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___188_15595.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___188_15595.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___188_15595.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___188_15595.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___188_15595.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15594 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15598),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15600)) ->
                  let uu____15609 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15609
              | (FStar_Syntax_Syntax.Tm_bvar uu____15610,uu____15611) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15612,FStar_Syntax_Syntax.Tm_bvar uu____15613) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___142_15672 =
                    match uu___142_15672 with
                    | [] -> c
                    | bs ->
                        let uu____15694 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15694
                     in
                  let uu____15703 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15703 with
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
                                    let uu____15826 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15826
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
                  let mk_t t l uu___143_15901 =
                    match uu___143_15901 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15935 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15935 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16054 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16055 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16054
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16055 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16056,uu____16057) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16084 -> true
                    | uu____16101 -> false  in
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
                      (let uu____16142 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___189_16150 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___189_16150.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___189_16150.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___189_16150.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___189_16150.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___189_16150.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___189_16150.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___189_16150.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___189_16150.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___189_16150.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___189_16150.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___189_16150.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___189_16150.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___189_16150.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___189_16150.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___189_16150.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___189_16150.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___189_16150.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___189_16150.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___189_16150.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___189_16150.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___189_16150.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___189_16150.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___189_16150.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___189_16150.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___189_16150.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___189_16150.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___189_16150.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___189_16150.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___189_16150.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___189_16150.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___189_16150.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___189_16150.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___189_16150.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___189_16150.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___189_16150.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16142 with
                       | (uu____16153,ty,uu____16155) ->
                           let uu____16156 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16156)
                     in
                  let uu____16157 =
                    let uu____16170 = maybe_eta t1  in
                    let uu____16175 = maybe_eta t2  in
                    (uu____16170, uu____16175)  in
                  (match uu____16157 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___190_16199 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___190_16199.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___190_16199.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___190_16199.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___190_16199.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___190_16199.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___190_16199.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___190_16199.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___190_16199.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16210 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16210
                       then
                         let uu____16211 = destruct_flex_t not_abs wl  in
                         (match uu____16211 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16226 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16226.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16226.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16226.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16226.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16226.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16226.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16226.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16226.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16238 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16238
                       then
                         let uu____16239 = destruct_flex_t not_abs wl  in
                         (match uu____16239 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16254 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16254.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16254.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16254.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16254.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16254.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16254.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16254.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16254.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16256 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16269,FStar_Syntax_Syntax.Tm_abs uu____16270) ->
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
                      (let uu____16355 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___189_16363 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___189_16363.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___189_16363.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___189_16363.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___189_16363.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___189_16363.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___189_16363.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___189_16363.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___189_16363.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___189_16363.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___189_16363.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___189_16363.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___189_16363.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___189_16363.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___189_16363.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___189_16363.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___189_16363.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___189_16363.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___189_16363.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___189_16363.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___189_16363.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___189_16363.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___189_16363.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___189_16363.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___189_16363.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___189_16363.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___189_16363.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___189_16363.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___189_16363.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___189_16363.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___189_16363.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___189_16363.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___189_16363.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___189_16363.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___189_16363.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___189_16363.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16355 with
                       | (uu____16366,ty,uu____16368) ->
                           let uu____16369 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16369)
                     in
                  let uu____16370 =
                    let uu____16383 = maybe_eta t1  in
                    let uu____16388 = maybe_eta t2  in
                    (uu____16383, uu____16388)  in
                  (match uu____16370 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___190_16412 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___190_16412.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___190_16412.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___190_16412.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___190_16412.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___190_16412.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___190_16412.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___190_16412.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___190_16412.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16423 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16423
                       then
                         let uu____16424 = destruct_flex_t not_abs wl  in
                         (match uu____16424 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16439 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16439.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16439.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16439.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16439.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16439.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16439.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16439.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16439.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16451 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16451
                       then
                         let uu____16452 = destruct_flex_t not_abs wl  in
                         (match uu____16452 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___191_16467 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___191_16467.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___191_16467.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___191_16467.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___191_16467.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___191_16467.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___191_16467.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___191_16467.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___191_16467.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16469 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16497 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16497) &&
                       (let uu____16501 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16501))
                      &&
                      (let uu____16508 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16508 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___144_16520 =
                             match uu___144_16520 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16521 -> true
                             | uu____16522 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16523 -> false)
                     in
                  let uu____16524 = as_refinement should_delta env wl t1  in
                  (match uu____16524 with
                   | (x11,phi1) ->
                       let uu____16531 = as_refinement should_delta env wl t2
                          in
                       (match uu____16531 with
                        | (x21,phi21) ->
                            let uu____16538 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16538 with
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
                                   let uu____16604 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16604
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16616 =
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
                                   let uu____16627 =
                                     let uu____16632 =
                                       let uu____16639 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16639]  in
                                     mk_t_problem wl1 uu____16632 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16627 with
                                    | (ref_prob,wl2) ->
                                        let uu____16654 =
                                          solve env1
                                            (let uu___192_16656 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___192_16656.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___192_16656.smt_ok);
                                               tcenv = (uu___192_16656.tcenv);
                                               wl_implicits =
                                                 (uu___192_16656.wl_implicits)
                                             })
                                           in
                                        (match uu____16654 with
                                         | Failed uu____16663 -> fallback ()
                                         | Success uu____16668 ->
                                             let guard =
                                               let uu____16676 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16676
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___193_16685 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___193_16685.attempting);
                                                 wl_deferred =
                                                   (uu___193_16685.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___193_16685.defer_ok);
                                                 smt_ok =
                                                   (uu___193_16685.smt_ok);
                                                 tcenv =
                                                   (uu___193_16685.tcenv);
                                                 wl_implicits =
                                                   (uu___193_16685.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16687,FStar_Syntax_Syntax.Tm_uvar uu____16688) ->
                  let uu____16717 = destruct_flex_t t1 wl  in
                  (match uu____16717 with
                   | (f1,wl1) ->
                       let uu____16724 = destruct_flex_t t2 wl1  in
                       (match uu____16724 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16731;
                    FStar_Syntax_Syntax.pos = uu____16732;
                    FStar_Syntax_Syntax.vars = uu____16733;_},uu____16734),FStar_Syntax_Syntax.Tm_uvar
                 uu____16735) ->
                  let uu____16784 = destruct_flex_t t1 wl  in
                  (match uu____16784 with
                   | (f1,wl1) ->
                       let uu____16791 = destruct_flex_t t2 wl1  in
                       (match uu____16791 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16798,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16799;
                    FStar_Syntax_Syntax.pos = uu____16800;
                    FStar_Syntax_Syntax.vars = uu____16801;_},uu____16802))
                  ->
                  let uu____16851 = destruct_flex_t t1 wl  in
                  (match uu____16851 with
                   | (f1,wl1) ->
                       let uu____16858 = destruct_flex_t t2 wl1  in
                       (match uu____16858 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16865;
                    FStar_Syntax_Syntax.pos = uu____16866;
                    FStar_Syntax_Syntax.vars = uu____16867;_},uu____16868),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16869;
                    FStar_Syntax_Syntax.pos = uu____16870;
                    FStar_Syntax_Syntax.vars = uu____16871;_},uu____16872))
                  ->
                  let uu____16941 = destruct_flex_t t1 wl  in
                  (match uu____16941 with
                   | (f1,wl1) ->
                       let uu____16948 = destruct_flex_t t2 wl1  in
                       (match uu____16948 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16955,uu____16956) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16971 = destruct_flex_t t1 wl  in
                  (match uu____16971 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16978;
                    FStar_Syntax_Syntax.pos = uu____16979;
                    FStar_Syntax_Syntax.vars = uu____16980;_},uu____16981),uu____16982)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17017 = destruct_flex_t t1 wl  in
                  (match uu____17017 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17024,FStar_Syntax_Syntax.Tm_uvar uu____17025) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17040,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17041;
                    FStar_Syntax_Syntax.pos = uu____17042;
                    FStar_Syntax_Syntax.vars = uu____17043;_},uu____17044))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17079,FStar_Syntax_Syntax.Tm_arrow uu____17080) ->
                  solve_t' env
                    (let uu___194_17108 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___194_17108.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___194_17108.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___194_17108.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___194_17108.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___194_17108.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___194_17108.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___194_17108.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___194_17108.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___194_17108.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17109;
                    FStar_Syntax_Syntax.pos = uu____17110;
                    FStar_Syntax_Syntax.vars = uu____17111;_},uu____17112),FStar_Syntax_Syntax.Tm_arrow
                 uu____17113) ->
                  solve_t' env
                    (let uu___194_17161 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___194_17161.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___194_17161.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___194_17161.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___194_17161.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___194_17161.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___194_17161.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___194_17161.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___194_17161.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___194_17161.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17162,FStar_Syntax_Syntax.Tm_uvar uu____17163) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____17178,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17179;
                    FStar_Syntax_Syntax.pos = uu____17180;
                    FStar_Syntax_Syntax.vars = uu____17181;_},uu____17182))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____17217,uu____17218) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17233;
                    FStar_Syntax_Syntax.pos = uu____17234;
                    FStar_Syntax_Syntax.vars = uu____17235;_},uu____17236),uu____17237)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____17272,uu____17273) ->
                  let t21 =
                    let uu____17281 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17281  in
                  solve_t env
                    (let uu___195_17307 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17307.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17307.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___195_17307.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___195_17307.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17307.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17307.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17307.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17307.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17307.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17308,FStar_Syntax_Syntax.Tm_refine uu____17309) ->
                  let t11 =
                    let uu____17317 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17317  in
                  solve_t env
                    (let uu___196_17343 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___196_17343.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___196_17343.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___196_17343.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___196_17343.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___196_17343.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___196_17343.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___196_17343.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___196_17343.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___196_17343.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let uu____17420 =
                    mk_t_problem wl [] orig s1 FStar_TypeChecker_Common.EQ s2
                      FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____17420 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____17641 = br1  in
                             (match uu____17641 with
                              | (p1,w1,uu____17666) ->
                                  let uu____17683 = br2  in
                                  (match uu____17683 with
                                   | (p2,w2,uu____17702) ->
                                       let uu____17707 =
                                         let uu____17708 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____17708  in
                                       if uu____17707
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____17724 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____17724 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____17757 = br2  in
                                              (match uu____17757 with
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
                                                     let uu____17792 =
                                                       p_scope orig  in
                                                     let uu____17799 =
                                                       let uu____17806 =
                                                         FStar_Syntax_Syntax.pat_bvs
                                                           p11
                                                          in
                                                       FStar_All.pipe_left
                                                         (FStar_List.map
                                                            FStar_Syntax_Syntax.mk_binder)
                                                         uu____17806
                                                        in
                                                     FStar_List.append
                                                       uu____17792
                                                       uu____17799
                                                      in
                                                   let uu____17821 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____17844,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____17861) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____17904 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____17904
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____17821
                                                     (fun uu____17946  ->
                                                        match uu____17946
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____17967 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____17967
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____17982
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____17982
                                                                   (fun
                                                                    uu____18006
                                                                     ->
                                                                    match uu____18006
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
                         | uu____18091 -> FStar_Pervasives_Native.None  in
                       let by_smt wl2 =
                         let uu____18134 =
                           guard_of_prob env wl2 problem t1 t2  in
                         match uu____18134 with
                         | (guard,wl3) ->
                             let uu____18141 =
                               solve_prob orig
                                 (FStar_Pervasives_Native.Some guard) [] wl3
                                in
                             solve env uu____18141
                          in
                       let uu____18142 = solve_branches wl1 brs1 brs2  in
                       (match uu____18142 with
                        | FStar_Pervasives_Native.None  ->
                            if wl1.smt_ok
                            then by_smt wl1
                            else
                              giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
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
                                  by_smt wl3))))
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
           (fun uu____21016  ->
              match uu____21016 with
              | (uu____21027,tm,uu____21029,uu____21030,uu____21031) ->
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
      let uu____21064 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21064 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21082 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21110  ->
                match uu____21110 with
                | (u1,u2) ->
                    let uu____21117 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21118 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21117 uu____21118))
         in
      FStar_All.pipe_right uu____21082 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21145,[])) -> "{}"
      | uu____21170 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21193 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21193
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21196 =
              FStar_List.map
                (fun uu____21206  ->
                   match uu____21206 with
                   | (uu____21211,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21196 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21216 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21216 imps
  
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
                  let uu____21269 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21269
                  then
                    let uu____21270 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21271 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21270
                      (rel_to_string rel) uu____21271
                  else "TOP"  in
                let uu____21273 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21273 with
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
              let uu____21330 =
                let uu____21333 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21333
                 in
              FStar_Syntax_Syntax.new_bv uu____21330 t1  in
            let uu____21336 =
              let uu____21341 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21341
               in
            match uu____21336 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____21397 = FStar_Options.eager_inference ()  in
          if uu____21397
          then
            let uu___200_21398 = probs  in
            {
              attempting = (uu___200_21398.attempting);
              wl_deferred = (uu___200_21398.wl_deferred);
              ctr = (uu___200_21398.ctr);
              defer_ok = false;
              smt_ok = (uu___200_21398.smt_ok);
              tcenv = (uu___200_21398.tcenv);
              wl_implicits = (uu___200_21398.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____21418 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21418
              then
                let uu____21419 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21419
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
          ((let uu____21441 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21441
            then
              let uu____21442 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21442
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21446 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21446
             then
               let uu____21447 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21447
             else ());
            (let f2 =
               let uu____21450 =
                 let uu____21451 = FStar_Syntax_Util.unmeta f1  in
                 uu____21451.FStar_Syntax_Syntax.n  in
               match uu____21450 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21455 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___201_21456 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___201_21456.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___201_21456.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___201_21456.FStar_TypeChecker_Env.implicits)
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
            let uu____21570 =
              let uu____21571 =
                let uu____21572 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21572;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21571  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21570
  
let with_guard_no_simp :
  'Auu____21587 .
    'Auu____21587 ->
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
            let uu____21610 =
              let uu____21611 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21611;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21610
  
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
          (let uu____21651 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21651
           then
             let uu____21652 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21653 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21652
               uu____21653
           else ());
          (let uu____21655 =
             let uu____21660 = empty_worklist env  in
             let uu____21661 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____21660 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____21661
              in
           match uu____21655 with
           | (prob,wl) ->
               let g =
                 let uu____21669 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21689  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21669  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21733 = try_teq true env t1 t2  in
        match uu____21733 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21737 = FStar_TypeChecker_Env.get_range env  in
              let uu____21738 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21737 uu____21738);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21745 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21745
              then
                let uu____21746 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21747 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21748 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21746
                  uu____21747 uu____21748
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
          let uu____21770 = FStar_TypeChecker_Env.get_range env  in
          let uu____21771 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21770 uu____21771
  
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
        (let uu____21796 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21796
         then
           let uu____21797 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21798 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21797 uu____21798
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21801 =
           let uu____21808 = empty_worklist env  in
           let uu____21809 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____21808 env c1 rel c2 FStar_Pervasives_Native.None
             uu____21809 "sub_comp"
            in
         match uu____21801 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21819 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21839  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21819)
  
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
      fun uu____21894  ->
        match uu____21894 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21937 =
                 let uu____21942 =
                   let uu____21943 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21944 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21943 uu____21944
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21942)  in
               let uu____21945 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21937 uu____21945)
               in
            let equiv1 v1 v' =
              let uu____21957 =
                let uu____21962 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21963 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21962, uu____21963)  in
              match uu____21957 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21982 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22012 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22012 with
                      | FStar_Syntax_Syntax.U_unif uu____22019 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22048  ->
                                    match uu____22048 with
                                    | (u,v') ->
                                        let uu____22057 = equiv1 v1 v'  in
                                        if uu____22057
                                        then
                                          let uu____22060 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22060 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22076 -> []))
               in
            let uu____22081 =
              let wl =
                let uu___202_22085 = empty_worklist env  in
                {
                  attempting = (uu___202_22085.attempting);
                  wl_deferred = (uu___202_22085.wl_deferred);
                  ctr = (uu___202_22085.ctr);
                  defer_ok = false;
                  smt_ok = (uu___202_22085.smt_ok);
                  tcenv = (uu___202_22085.tcenv);
                  wl_implicits = (uu___202_22085.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22103  ->
                      match uu____22103 with
                      | (lb,v1) ->
                          let uu____22110 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22110 with
                           | USolved wl1 -> ()
                           | uu____22112 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22122 =
              match uu____22122 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22131) -> true
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
                      uu____22154,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22156,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22167) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22174,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22182 -> false)
               in
            let uu____22187 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22202  ->
                      match uu____22202 with
                      | (u,v1) ->
                          let uu____22209 = check_ineq (u, v1)  in
                          if uu____22209
                          then true
                          else
                            ((let uu____22212 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22212
                              then
                                let uu____22213 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22214 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22213
                                  uu____22214
                              else ());
                             false)))
               in
            if uu____22187
            then ()
            else
              ((let uu____22218 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22218
                then
                  ((let uu____22220 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22220);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22230 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22230))
                else ());
               (let uu____22240 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22240))
  
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
        let fail1 uu____22307 =
          match uu____22307 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___203_22328 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___203_22328.attempting);
            wl_deferred = (uu___203_22328.wl_deferred);
            ctr = (uu___203_22328.ctr);
            defer_ok;
            smt_ok = (uu___203_22328.smt_ok);
            tcenv = (uu___203_22328.tcenv);
            wl_implicits = (uu___203_22328.wl_implicits)
          }  in
        (let uu____22330 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22330
         then
           let uu____22331 = FStar_Util.string_of_bool defer_ok  in
           let uu____22332 = wl_to_string wl  in
           let uu____22333 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22331 uu____22332 uu____22333
         else ());
        (let g1 =
           let uu____22346 = solve_and_commit env wl fail1  in
           match uu____22346 with
           | FStar_Pervasives_Native.Some
               (uu____22353::uu____22354,uu____22355) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___204_22380 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___204_22380.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___204_22380.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22391 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___205_22399 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___205_22399.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___205_22399.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___205_22399.FStar_TypeChecker_Env.implicits)
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
    let uu____22447 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22447 with
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
            let uu___206_22570 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___206_22570.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___206_22570.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___206_22570.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22571 =
            let uu____22572 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22572  in
          if uu____22571
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22580 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22581 =
                       let uu____22582 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22582
                        in
                     FStar_Errors.diag uu____22580 uu____22581)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22586 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22587 =
                        let uu____22588 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22588
                         in
                      FStar_Errors.diag uu____22586 uu____22587)
                   else ();
                   (let uu____22591 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22591 "discharge_guard'"
                      env vc1);
                   (let uu____22592 = check_trivial vc1  in
                    match uu____22592 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22599 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22600 =
                                let uu____22601 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22601
                                 in
                              FStar_Errors.diag uu____22599 uu____22600)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22606 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22607 =
                                let uu____22608 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22608
                                 in
                              FStar_Errors.diag uu____22606 uu____22607)
                           else ();
                           (let vcs =
                              let uu____22621 = FStar_Options.use_tactics ()
                                 in
                              if uu____22621
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22643  ->
                                     (let uu____22645 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22645);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22688  ->
                                              match uu____22688 with
                                              | (env1,goal,opts) ->
                                                  let uu____22704 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22704, opts)))))
                              else
                                (let uu____22706 =
                                   let uu____22713 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22713)  in
                                 [uu____22706])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22750  ->
                                    match uu____22750 with
                                    | (env1,goal,opts) ->
                                        let uu____22766 = check_trivial goal
                                           in
                                        (match uu____22766 with
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
                                                (let uu____22774 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22775 =
                                                   let uu____22776 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22777 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22776 uu____22777
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22774 uu____22775)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22780 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22781 =
                                                   let uu____22782 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22782
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22780 uu____22781)
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
      let uu____22796 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22796 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22803 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22803
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22814 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22814 with
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
            let uu____22847 = FStar_Syntax_Util.head_and_args u  in
            match uu____22847 with
            | (hd1,uu____22863) ->
                let uu____22884 =
                  let uu____22885 = FStar_Syntax_Subst.compress u  in
                  uu____22885.FStar_Syntax_Syntax.n  in
                (match uu____22884 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____22888 -> true
                 | uu____22903 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____22923 = acc  in
            match uu____22923 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22985 = hd1  in
                     (match uu____22985 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23002 = unresolved tm  in
                             if uu____23002
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___207_23015 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___207_23015.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___207_23015.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___207_23015.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___207_23015.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___207_23015.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___207_23015.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___207_23015.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___207_23015.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___207_23015.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___207_23015.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___207_23015.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___207_23015.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___207_23015.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___207_23015.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___207_23015.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___207_23015.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___207_23015.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___207_23015.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___207_23015.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___207_23015.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___207_23015.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___207_23015.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___207_23015.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___207_23015.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___207_23015.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___207_23015.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___207_23015.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___207_23015.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___207_23015.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___207_23015.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___207_23015.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___207_23015.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___207_23015.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___207_23015.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___207_23015.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___207_23015.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___207_23015.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___208_23018 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___208_23018.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___208_23018.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___208_23018.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___208_23018.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___208_23018.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___208_23018.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___208_23018.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___208_23018.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___208_23018.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___208_23018.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___208_23018.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___208_23018.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___208_23018.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___208_23018.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___208_23018.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___208_23018.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___208_23018.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___208_23018.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___208_23018.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___208_23018.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___208_23018.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___208_23018.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___208_23018.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___208_23018.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___208_23018.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___208_23018.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___208_23018.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___208_23018.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___208_23018.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___208_23018.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___208_23018.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___208_23018.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___208_23018.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___208_23018.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___208_23018.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___208_23018.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___208_23018.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____23021 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____23021
                                 then
                                   let uu____23022 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____23023 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____23024 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____23025 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____23022 uu____23023 uu____23024
                                     reason uu____23025
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e when FStar_Errors.handleable e ->
                                       ((let uu____23036 =
                                           let uu____23045 =
                                             let uu____23052 =
                                               let uu____23053 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____23054 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____23053 uu____23054
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____23052, r)
                                              in
                                           [uu____23045]  in
                                         FStar_Errors.add_errors uu____23036);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___211_23068 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___211_23068.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___211_23068.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___211_23068.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____23071 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____23078  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____23071 with
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
          let uu___212_23090 = g  in
          let uu____23091 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___212_23090.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___212_23090.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___212_23090.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23091
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
        let uu____23145 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23145 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23156 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23156
      | (reason,e,ctx_u,r,should_check)::uu____23162 ->
          let uu____23185 =
            let uu____23190 =
              let uu____23191 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23192 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____23193 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____23191 uu____23192 reason uu____23193
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23190)
             in
          FStar_Errors.raise_error uu____23185 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___213_23204 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___213_23204.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___213_23204.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___213_23204.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23219 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23219 with
      | FStar_Pervasives_Native.Some uu____23225 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23241 = try_teq false env t1 t2  in
        match uu____23241 with
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
        (let uu____23275 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23275
         then
           let uu____23276 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23277 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23276
             uu____23277
         else ());
        (let uu____23279 =
           let uu____23286 = empty_worklist env  in
           new_t_prob uu____23286 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23279 with
         | (prob,x,wl) ->
             let g =
               let uu____23299 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23319  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23299  in
             ((let uu____23349 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23349
               then
                 let uu____23350 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23351 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23352 =
                   let uu____23353 = FStar_Util.must g  in
                   guard_to_string env uu____23353  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23350 uu____23351 uu____23352
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
        let uu____23387 = check_subtyping env t1 t2  in
        match uu____23387 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23406 =
              let uu____23407 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23407 g  in
            FStar_Pervasives_Native.Some uu____23406
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23425 = check_subtyping env t1 t2  in
        match uu____23425 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23444 =
              let uu____23445 =
                let uu____23446 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23446]  in
              close_guard env uu____23445 g  in
            FStar_Pervasives_Native.Some uu____23444
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23475 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23475
         then
           let uu____23476 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23477 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23476
             uu____23477
         else ());
        (let uu____23479 =
           let uu____23486 = empty_worklist env  in
           new_t_prob uu____23486 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____23479 with
         | (prob,x,wl) ->
             let g =
               let uu____23493 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23513  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23493  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23544 =
                      let uu____23545 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23545]  in
                    close_guard env uu____23544 g1  in
                  discharge_guard_nosmt env g2))
  