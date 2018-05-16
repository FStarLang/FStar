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
          let uu___304_160 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___304_160.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___304_160.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___304_160.FStar_TypeChecker_Env.implicits)
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
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____245 =
            let uu____246 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____246  in
          if uu____245
          then ()
          else
            (let uu____248 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____248 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____271 =
            let uu____272 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____272  in
          if uu____271
          then ()
          else
            (let uu____274 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____274 t)
  
let (def_check_guard_wf :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.FStar_TypeChecker_Env.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___305_309 = g  in
          let uu____310 =
            let uu____311 =
              let uu____312 =
                let uu____319 =
                  let uu____320 =
                    let uu____335 =
                      let uu____344 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____344]  in
                    (f, uu____335)  in
                  FStar_Syntax_Syntax.Tm_app uu____320  in
                FStar_Syntax_Syntax.mk uu____319  in
              uu____312 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_16  -> FStar_TypeChecker_Common.NonTrivial _0_16)
              uu____311
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____310;
            FStar_TypeChecker_Env.deferred =
              (uu___305_309.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___305_309.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___305_309.FStar_TypeChecker_Env.implicits)
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
          let uu___306_392 = g  in
          let uu____393 =
            let uu____394 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____394  in
          {
            FStar_TypeChecker_Env.guard_f = uu____393;
            FStar_TypeChecker_Env.deferred =
              (uu___306_392.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___306_392.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___306_392.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____400 -> failwith "impossible"
  
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
          let uu____415 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____415
  
let (check_trivial :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Common.guard_formula)
  =
  fun t  ->
    let uu____425 =
      let uu____426 = FStar_Syntax_Util.unmeta t  in
      uu____426.FStar_Syntax_Syntax.n  in
    match uu____425 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____430 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____471 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____471;
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
                       let uu____556 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____556
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___307_558 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___307_558.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___307_558.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___307_558.FStar_TypeChecker_Env.implicits)
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
               let uu____599 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____599
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
            let uu___308_618 = g  in
            let uu____619 =
              let uu____620 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____620  in
            {
              FStar_TypeChecker_Env.guard_f = uu____619;
              FStar_TypeChecker_Env.deferred =
                (uu___308_618.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___308_618.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___308_618.FStar_TypeChecker_Env.implicits)
            }
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____649 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____679 -> false
  
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
                  let uu____966 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____966;
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
                   (let uu___309_1000 = wl  in
                    {
                      attempting = (uu___309_1000.attempting);
                      wl_deferred = (uu___309_1000.wl_deferred);
                      ctr = (uu___309_1000.ctr);
                      defer_ok = (uu___309_1000.defer_ok);
                      smt_ok = (uu___309_1000.smt_ok);
                      tcenv = (uu___309_1000.tcenv);
                      wl_implicits = ((reason, t, ctx_uvar, r) ::
                        (wl.wl_implicits))
                    })))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,worklist)
            FStar_Pervasives_Native.tuple3)
  =
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___310_1040 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___310_1040.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___310_1040.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___310_1040.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___310_1040.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___310_1040.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___310_1040.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___310_1040.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___310_1040.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___310_1040.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___310_1040.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___310_1040.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___310_1040.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___310_1040.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___310_1040.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___310_1040.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___310_1040.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___310_1040.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___310_1040.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___310_1040.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___310_1040.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___310_1040.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___310_1040.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___310_1040.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___310_1040.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___310_1040.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___310_1040.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___310_1040.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___310_1040.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___310_1040.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___310_1040.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___310_1040.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___310_1040.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___310_1040.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___310_1040.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___310_1040.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___310_1040.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___310_1040.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___310_1040.FStar_TypeChecker_Env.dep_graph)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____1042 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____1042 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____1077 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1107 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____1132 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1138 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1144 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___271_1159  ->
    match uu___271_1159 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1165 = FStar_Syntax_Util.head_and_args t  in
    match uu____1165 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1224 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1225 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1239 =
                     let uu____1240 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1240  in
                   FStar_Util.format1 "@<%s>" uu____1239
                in
             let uu____1243 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1224 uu____1225 uu____1243
         | uu____1244 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___272_1254  ->
      match uu___272_1254 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1258 =
            let uu____1261 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1262 =
              let uu____1265 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1266 =
                let uu____1269 =
                  let uu____1272 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1272]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1269
                 in
              uu____1265 :: uu____1266  in
            uu____1261 :: uu____1262  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1258
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1276 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1277 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1278 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1276 uu____1277
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1278
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___273_1288  ->
      match uu___273_1288 with
      | UNIV (u,t) ->
          let x =
            let uu____1292 = FStar_Options.hide_uvar_nums ()  in
            if uu____1292
            then "?"
            else
              (let uu____1294 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1294 FStar_Util.string_of_int)
             in
          let uu____1295 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1295
      | TERM (u,t) ->
          let x =
            let uu____1299 = FStar_Options.hide_uvar_nums ()  in
            if uu____1299
            then "?"
            else
              (let uu____1301 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1301 FStar_Util.string_of_int)
             in
          let uu____1302 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1302
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1317 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1317 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1331 =
      let uu____1334 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1334
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1331 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1347 .
    (FStar_Syntax_Syntax.term,'Auu____1347) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1365 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1383  ->
              match uu____1383 with
              | (x,uu____1389) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1365 (FStar_String.concat " ")
  
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
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1427 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1427
         then
           let uu____1428 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1428
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___274_1434  ->
    match uu___274_1434 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1439 .
    'Auu____1439 FStar_TypeChecker_Common.problem ->
      'Auu____1439 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___311_1451 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___311_1451.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___311_1451.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___311_1451.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___311_1451.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___311_1451.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___311_1451.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___311_1451.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1458 .
    'Auu____1458 FStar_TypeChecker_Common.problem ->
      'Auu____1458 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___275_1475  ->
    match uu___275_1475 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.TProb _0_17)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.CProb _0_18)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___276_1490  ->
    match uu___276_1490 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___312_1496 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___312_1496.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___312_1496.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___312_1496.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___312_1496.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___312_1496.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___312_1496.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___312_1496.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___312_1496.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___312_1496.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___313_1504 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___313_1504.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___313_1504.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___313_1504.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___313_1504.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___313_1504.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___313_1504.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___313_1504.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___313_1504.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___313_1504.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___277_1516  ->
      match uu___277_1516 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___278_1521  ->
    match uu___278_1521 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___279_1532  ->
    match uu___279_1532 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___280_1545  ->
    match uu___280_1545 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___281_1558  ->
    match uu___281_1558 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___282_1571  ->
    match uu___282_1571 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___283_1584  ->
    match uu___283_1584 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___284_1595  ->
    match uu___284_1595 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1610 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1610) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1638 =
          let uu____1639 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1639  in
        if uu____1638
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1673)::bs ->
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
          let uu____1713 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1731 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1731]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1713
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1751 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1769 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1769]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1751
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1802 =
          let uu____1803 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1803  in
        if uu____1802
        then ()
        else
          (let uu____1805 =
             let uu____1808 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1808
              in
           def_check_closed_in (p_loc prob) msg uu____1805 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1846 =
          let uu____1847 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1847  in
        if uu____1846
        then ()
        else
          (let uu____1849 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1849)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1864 =
        let uu____1865 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1865  in
      if uu____1864
      then ()
      else
        (let msgf m =
           let uu____1873 =
             let uu____1874 =
               let uu____1875 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1875 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1874  in
           Prims.strcat msg uu____1873  in
         (let uu____1877 = msgf "scope"  in
          let uu____1878 = p_scope prob  in
          def_scope_wf uu____1877 (p_loc prob) uu____1878);
         (let uu____1886 = msgf "guard"  in
          def_check_scoped uu____1886 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1891 = msgf "lhs"  in
                def_check_scoped uu____1891 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1892 = msgf "rhs"  in
                def_check_scoped uu____1892 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1897 = msgf "lhs"  in
                def_check_scoped_comp uu____1897 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1898 = msgf "rhs"  in
                def_check_scoped_comp uu____1898 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___314_1914 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___314_1914.wl_deferred);
          ctr = (uu___314_1914.ctr);
          defer_ok = (uu___314_1914.defer_ok);
          smt_ok;
          tcenv = (uu___314_1914.tcenv);
          wl_implicits = (uu___314_1914.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1921 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1921,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___315_1944 = empty_worklist env  in
      let uu____1945 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1945;
        wl_deferred = (uu___315_1944.wl_deferred);
        ctr = (uu___315_1944.ctr);
        defer_ok = (uu___315_1944.defer_ok);
        smt_ok = (uu___315_1944.smt_ok);
        tcenv = (uu___315_1944.tcenv);
        wl_implicits = (uu___315_1944.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___316_1965 = wl  in
        {
          attempting = (uu___316_1965.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___316_1965.ctr);
          defer_ok = (uu___316_1965.defer_ok);
          smt_ok = (uu___316_1965.smt_ok);
          tcenv = (uu___316_1965.tcenv);
          wl_implicits = (uu___316_1965.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___317_1987 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___317_1987.wl_deferred);
         ctr = (uu___317_1987.ctr);
         defer_ok = (uu___317_1987.defer_ok);
         smt_ok = (uu___317_1987.smt_ok);
         tcenv = (uu___317_1987.tcenv);
         wl_implicits = (uu___317_1987.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1998 .
    worklist ->
      'Auu____1998 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____2027 = FStar_Syntax_Util.type_u ()  in
          match uu____2027 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____2039 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____2039 with
               | (uu____2050,tt,wl1) ->
                   let uu____2053 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____2053, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___285_2058  ->
    match uu___285_2058 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2074 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2074 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____2084  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2182 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2182 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2182 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2182 FStar_TypeChecker_Common.problem,worklist)
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
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None  -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____2259 =
                          let uu____2266 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2266]  in
                        FStar_List.append scope uu____2259
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2297 =
                      let uu____2300 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2300  in
                    FStar_List.append uu____2297
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2313 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2313 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2332 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2332;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
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
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu____2396 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2396 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
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
                  def_check_prob (Prims.strcat reason ".mk_c.arg") orig;
                  (let uu____2475 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2475 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2511 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2511 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2511 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2511 FStar_TypeChecker_Common.problem,worklist)
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
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2575 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2575]  in
                        let uu____2588 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2588
                     in
                  let uu____2591 =
                    let uu____2598 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___318_2606 = wl  in
                       {
                         attempting = (uu___318_2606.attempting);
                         wl_deferred = (uu___318_2606.wl_deferred);
                         ctr = (uu___318_2606.ctr);
                         defer_ok = (uu___318_2606.defer_ok);
                         smt_ok = (uu___318_2606.smt_ok);
                         tcenv = env;
                         wl_implicits = (uu___318_2606.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2598
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2591 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2618 =
                              let uu____2623 =
                                let uu____2624 =
                                  let uu____2631 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2631
                                   in
                                [uu____2624]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2623  in
                            uu____2618 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2655 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2655;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = subject;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = [reason];
                          FStar_TypeChecker_Common.loc = loc;
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem)
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let p =
                let uu____2697 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2697;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStar_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }  in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
  
let guard_on_element :
  'Auu____2709 .
    worklist ->
      'Auu____2709 FStar_TypeChecker_Common.problem ->
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
              let uu____2742 =
                let uu____2745 =
                  let uu____2746 =
                    let uu____2753 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2753)  in
                  FStar_Syntax_Syntax.NT uu____2746  in
                [uu____2745]  in
              FStar_Syntax_Subst.subst uu____2742 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2773 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2773
        then
          let uu____2774 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2775 = prob_to_string env d  in
          let uu____2776 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2774 uu____2775 uu____2776 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2782 -> failwith "impossible"  in
           let uu____2783 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2795 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2796 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2795, uu____2796)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2800 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2801 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2800, uu____2801)
              in
           match uu____2783 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___286_2819  ->
            match uu___286_2819 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2831 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2835 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  def_check_closed_in t.FStar_Syntax_Syntax.pos "commit"
                    uu____2835 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___287_2860  ->
           match uu___287_2860 with
           | UNIV uu____2863 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2870 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2870
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
        (fun uu___288_2894  ->
           match uu___288_2894 with
           | UNIV (u',t) ->
               let uu____2899 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2899
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2903 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2914 =
        let uu____2915 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2915
         in
      FStar_Syntax_Subst.compress uu____2914
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2926 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2926
  
let norm_arg :
  'Auu____2933 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2933) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2933)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2956 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2956, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2997  ->
              match uu____2997 with
              | (x,imp) ->
                  let uu____3008 =
                    let uu___319_3009 = x  in
                    let uu____3010 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___319_3009.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___319_3009.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3010
                    }  in
                  (uu____3008, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3031 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3031
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3035 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3035
        | uu____3038 -> u2  in
      let uu____3039 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3039
  
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
                (let uu____3161 = norm_refinement env t12  in
                 match uu____3161 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3178;
                     FStar_Syntax_Syntax.vars = uu____3179;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3205 =
                       let uu____3206 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3207 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3206 uu____3207
                        in
                     failwith uu____3205)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3223 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3223
          | FStar_Syntax_Syntax.Tm_uinst uu____3224 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3263 =
                   let uu____3264 = FStar_Syntax_Subst.compress t1'  in
                   uu____3264.FStar_Syntax_Syntax.n  in
                 match uu____3263 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3281 -> aux true t1'
                 | uu____3288 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3305 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3338 =
                   let uu____3339 = FStar_Syntax_Subst.compress t1'  in
                   uu____3339.FStar_Syntax_Syntax.n  in
                 match uu____3338 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3356 -> aux true t1'
                 | uu____3363 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3380 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3427 =
                   let uu____3428 = FStar_Syntax_Subst.compress t1'  in
                   uu____3428.FStar_Syntax_Syntax.n  in
                 match uu____3427 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3445 -> aux true t1'
                 | uu____3452 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3469 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3486 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3503 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3520 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3537 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3566 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3599 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3622 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3653 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3682 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3721 ->
              let uu____3728 =
                let uu____3729 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3730 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3729 uu____3730
                 in
              failwith uu____3728
          | FStar_Syntax_Syntax.Tm_ascribed uu____3745 ->
              let uu____3772 =
                let uu____3773 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3774 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3773 uu____3774
                 in
              failwith uu____3772
          | FStar_Syntax_Syntax.Tm_delayed uu____3789 ->
              let uu____3814 =
                let uu____3815 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3816 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3815 uu____3816
                 in
              failwith uu____3814
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3831 =
                let uu____3832 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3833 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3832 uu____3833
                 in
              failwith uu____3831
           in
        let uu____3848 = whnf env t1  in aux false uu____3848
  
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
      let uu____3894 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3894 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3930 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3930, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3941 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3941 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3968 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3968 with
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
  fun uu____4055  ->
    match uu____4055 with
    | (t_base,refopt) ->
        let uu____4088 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4088 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4128 =
      let uu____4131 =
        let uu____4134 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4157  ->
                  match uu____4157 with | (uu____4164,uu____4165,x) -> x))
           in
        FStar_List.append wl.attempting uu____4134  in
      FStar_List.map (wl_prob_to_string wl) uu____4131  in
    FStar_All.pipe_right uu____4128 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4179 .
    ('Auu____4179,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4190  ->
    match uu____4190 with
    | (uu____4197,c,args) ->
        let uu____4200 = print_ctx_uvar c  in
        let uu____4201 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4200 uu____4201
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4207 = FStar_Syntax_Util.head_and_args t  in
    match uu____4207 with
    | (head1,_args) ->
        let uu____4244 =
          let uu____4245 = FStar_Syntax_Subst.compress head1  in
          uu____4245.FStar_Syntax_Syntax.n  in
        (match uu____4244 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4248 -> true
         | uu____4263 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4269 = FStar_Syntax_Util.head_and_args t  in
    match uu____4269 with
    | (head1,_args) ->
        let uu____4306 =
          let uu____4307 = FStar_Syntax_Subst.compress head1  in
          uu____4307.FStar_Syntax_Syntax.n  in
        (match uu____4306 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4311) -> u
         | uu____4332 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4355 = FStar_Syntax_Util.head_and_args t  in
      match uu____4355 with
      | (head1,args) ->
          let uu____4396 =
            let uu____4397 = FStar_Syntax_Subst.compress head1  in
            uu____4397.FStar_Syntax_Syntax.n  in
          (match uu____4396 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4405)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4448 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___289_4473  ->
                         match uu___289_4473 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4477 =
                               let uu____4478 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4478.FStar_Syntax_Syntax.n  in
                             (match uu____4477 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4482 -> false)
                         | uu____4483 -> true))
                  in
               (match uu____4448 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4505 =
                        FStar_List.collect
                          (fun uu___290_4515  ->
                             match uu___290_4515 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4519 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4519]
                             | uu____4520 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4505 FStar_List.rev  in
                    let uu____4537 =
                      let uu____4544 =
                        let uu____4551 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___291_4569  ->
                                  match uu___291_4569 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4573 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4573]
                                  | uu____4574 -> []))
                           in
                        FStar_All.pipe_right uu____4551 FStar_List.rev  in
                      let uu____4591 =
                        let uu____4594 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4594  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4544 uu____4591
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4537 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4623  ->
                                match uu____4623 with
                                | (x,i) ->
                                    let uu____4634 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4634, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4657  ->
                                match uu____4657 with
                                | (a,i) ->
                                    let uu____4668 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4668, i)) args_sol
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
           | uu____4684 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4704 =
          let uu____4725 =
            let uu____4726 = FStar_Syntax_Subst.compress k  in
            uu____4726.FStar_Syntax_Syntax.n  in
          match uu____4725 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4795 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4795)
              else
                (let uu____4825 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4825 with
                 | (ys',t1,uu____4856) ->
                     let uu____4861 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4861))
          | uu____4894 ->
              let uu____4895 =
                let uu____4900 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4900)  in
              ((ys, t), uu____4895)
           in
        match uu____4704 with
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
                 let uu____4977 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4977 c  in
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
               (let uu____5051 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5051
                then
                  let uu____5052 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5053 = print_ctx_uvar uv  in
                  let uu____5054 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5052 uu____5053 uu____5054
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5060 =
                   let uu____5061 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____5061  in
                 let uu____5062 =
                   let uu____5065 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5065
                    in
                 def_check_closed_in (p_loc prob) uu____5060 uu____5062 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5090 =
               let uu____5091 =
                 let uu____5092 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5093 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5092 uu____5093
                  in
               failwith uu____5091  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5143  ->
                       match uu____5143 with
                       | (a,i) ->
                           let uu____5156 =
                             let uu____5157 = FStar_Syntax_Subst.compress a
                                in
                             uu____5157.FStar_Syntax_Syntax.n  in
                           (match uu____5156 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5175 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5183 =
                 let uu____5184 = is_flex g  in Prims.op_Negation uu____5184
                  in
               if uu____5183
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5188 = destruct_flex_t g wl  in
                  match uu____5188 with
                  | ((uu____5193,uv1,args),wl1) ->
                      ((let uu____5198 = args_as_binders args  in
                        assign_solution uu____5198 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___320_5200 = wl1  in
              {
                attempting = (uu___320_5200.attempting);
                wl_deferred = (uu___320_5200.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___320_5200.defer_ok);
                smt_ok = (uu___320_5200.smt_ok);
                tcenv = (uu___320_5200.tcenv);
                wl_implicits = (uu___320_5200.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5221 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5221
         then
           let uu____5222 = FStar_Util.string_of_int pid  in
           let uu____5223 =
             let uu____5224 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5224 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5222 uu____5223
         else ());
        commit sol;
        (let uu___321_5231 = wl  in
         {
           attempting = (uu___321_5231.attempting);
           wl_deferred = (uu___321_5231.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___321_5231.defer_ok);
           smt_ok = (uu___321_5231.smt_ok);
           tcenv = (uu___321_5231.tcenv);
           wl_implicits = (uu___321_5231.wl_implicits)
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
             | (uu____5293,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5321 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5321
              in
           (let uu____5327 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5327
            then
              let uu____5328 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5329 =
                let uu____5330 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5330 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5328 uu____5329
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
        let uu____5355 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5355 FStar_Util.set_elements  in
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
      let uu____5389 = occurs uk t  in
      match uu____5389 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5418 =
                 let uu____5419 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5420 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5419 uu____5420
                  in
               FStar_Pervasives_Native.Some uu____5418)
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
            let uu____5509 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5509 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5553 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5601  ->
             match uu____5601 with
             | (x,uu____5611) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5624 = FStar_List.last bs  in
      match uu____5624 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5642) ->
          let uu____5647 =
            FStar_Util.prefix_until
              (fun uu___292_5662  ->
                 match uu___292_5662 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5664 -> false) g
             in
          (match uu____5647 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5677,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5713 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5713 with
        | (pfx,uu____5723) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5735 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5735 with
             | (uu____5742,src',wl1) ->
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
                 | uu____5842 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5843 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5897  ->
                  fun uu____5898  ->
                    match (uu____5897, uu____5898) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5979 =
                          let uu____5980 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5980
                           in
                        if uu____5979
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6005 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6005
                           then
                             let uu____6018 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6018)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5843 with | (isect,uu____6055) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6084 'Auu____6085 .
    (FStar_Syntax_Syntax.bv,'Auu____6084) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____6085) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6142  ->
              fun uu____6143  ->
                match (uu____6142, uu____6143) with
                | ((a,uu____6161),(b,uu____6163)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6178 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6178) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6208  ->
           match uu____6208 with
           | (y,uu____6214) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6223 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6223) FStar_Pervasives_Native.tuple2
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
                   let uu____6353 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6353
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6373 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6416 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6454 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6467 -> false
  
let string_of_option :
  'Auu____6474 .
    ('Auu____6474 -> Prims.string) ->
      'Auu____6474 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___293_6489  ->
      match uu___293_6489 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6495 = f x  in Prims.strcat "Some " uu____6495
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___294_6500  ->
    match uu___294_6500 with
    | MisMatch (d1,d2) ->
        let uu____6511 =
          let uu____6512 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6513 =
            let uu____6514 =
              let uu____6515 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6515 ")"  in
            Prims.strcat ") (" uu____6514  in
          Prims.strcat uu____6512 uu____6513  in
        Prims.strcat "MisMatch (" uu____6511
    | HeadMatch u ->
        let uu____6517 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6517
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___295_6522  ->
    match uu___295_6522 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6537 -> HeadMatch false
  
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
          let uu____6551 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6551 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6562 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6585 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6594 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6622 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6622
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6623 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6624 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6625 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6640 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6653 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6677) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6683,uu____6684) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6726) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6747;
             FStar_Syntax_Syntax.index = uu____6748;
             FStar_Syntax_Syntax.sort = t2;_},uu____6750)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6757 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6758 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6759 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6772 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6779 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6797 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6797
  
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
            let uu____6824 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6824
            then FullMatch
            else
              (let uu____6826 =
                 let uu____6835 =
                   let uu____6838 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6838  in
                 let uu____6839 =
                   let uu____6842 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6842  in
                 (uu____6835, uu____6839)  in
               MisMatch uu____6826)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6848),FStar_Syntax_Syntax.Tm_uinst (g,uu____6850)) ->
            let uu____6859 = head_matches env f g  in
            FStar_All.pipe_right uu____6859 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6862 = FStar_Const.eq_const c d  in
            if uu____6862
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6869),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6871)) ->
            let uu____6912 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6912
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6919),FStar_Syntax_Syntax.Tm_refine (y,uu____6921)) ->
            let uu____6930 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6930 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6932),uu____6933) ->
            let uu____6938 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6938 head_match
        | (uu____6939,FStar_Syntax_Syntax.Tm_refine (x,uu____6941)) ->
            let uu____6946 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6946 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6947,FStar_Syntax_Syntax.Tm_type
           uu____6948) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6949,FStar_Syntax_Syntax.Tm_arrow uu____6950) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6976),FStar_Syntax_Syntax.Tm_app (head',uu____6978))
            ->
            let uu____7019 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7019 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7021),uu____7022) ->
            let uu____7043 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7043 head_match
        | (uu____7044,FStar_Syntax_Syntax.Tm_app (head1,uu____7046)) ->
            let uu____7067 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7067 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7068,FStar_Syntax_Syntax.Tm_let
           uu____7069) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7094,FStar_Syntax_Syntax.Tm_match uu____7095) ->
            HeadMatch true
        | uu____7140 ->
            let uu____7145 =
              let uu____7154 = delta_depth_of_term env t11  in
              let uu____7157 = delta_depth_of_term env t21  in
              (uu____7154, uu____7157)  in
            MisMatch uu____7145
  
let head_matches_delta :
  'Auu____7174 .
    FStar_TypeChecker_Env.env ->
      'Auu____7174 ->
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
            (let uu____7223 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7223
             then
               let uu____7224 = FStar_Syntax_Print.term_to_string t  in
               let uu____7225 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7224 uu____7225
             else ());
            (let uu____7227 =
               let uu____7228 = FStar_Syntax_Util.un_uinst head1  in
               uu____7228.FStar_Syntax_Syntax.n  in
             match uu____7227 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7234 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7234 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7248 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7248
                        then
                          let uu____7249 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7249
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7251 ->
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
                      ((let uu____7262 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7262
                        then
                          let uu____7263 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7264 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7263
                            uu____7264
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7266 -> FStar_Pervasives_Native.None)
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
            (let uu____7404 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7404
             then
               let uu____7405 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7406 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7407 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7405
                 uu____7406 uu____7407
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7431 =
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
               match uu____7431 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7476 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7476 with
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
                  uu____7508),uu____7509)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7527 =
                      let uu____7536 = maybe_inline t11  in
                      let uu____7539 = maybe_inline t21  in
                      (uu____7536, uu____7539)  in
                    match uu____7527 with
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
                 (uu____7576,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7577))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7595 =
                      let uu____7604 = maybe_inline t11  in
                      let uu____7607 = maybe_inline t21  in
                      (uu____7604, uu____7607)  in
                    match uu____7595 with
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
             | MisMatch uu____7656 -> fail1 n_delta r t11 t21
             | uu____7665 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7678 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7678
           then
             let uu____7679 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7680 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7681 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7688 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7706 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7706
                    (fun uu____7740  ->
                       match uu____7740 with
                       | (t11,t21) ->
                           let uu____7747 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7748 =
                             let uu____7749 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7749  in
                           Prims.strcat uu____7747 uu____7748))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7679 uu____7680 uu____7681 uu____7688
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7761 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7761 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___296_7774  ->
    match uu___296_7774 with
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
      let uu___322_7811 = p  in
      let uu____7814 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7815 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___322_7811.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7814;
        FStar_TypeChecker_Common.relation =
          (uu___322_7811.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7815;
        FStar_TypeChecker_Common.element =
          (uu___322_7811.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___322_7811.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___322_7811.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___322_7811.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___322_7811.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___322_7811.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7829 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7829
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7834 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7856 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7856 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7864 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7864 with
           | (lh,lhs_args) ->
               let uu____7905 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7905 with
                | (rh,rhs_args) ->
                    let uu____7946 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7959,FStar_Syntax_Syntax.Tm_uvar uu____7960)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8041 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8064,uu____8065)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8082,FStar_Syntax_Syntax.Tm_uvar uu____8083)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8100,FStar_Syntax_Syntax.Tm_arrow uu____8101)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___323_8131 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___323_8131.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___323_8131.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___323_8131.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___323_8131.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___323_8131.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___323_8131.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___323_8131.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___323_8131.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___323_8131.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8134,FStar_Syntax_Syntax.Tm_type uu____8135)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___323_8153 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___323_8153.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___323_8153.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___323_8153.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___323_8153.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___323_8153.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___323_8153.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___323_8153.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___323_8153.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___323_8153.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8156,FStar_Syntax_Syntax.Tm_uvar uu____8157)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___323_8175 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___323_8175.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___323_8175.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___323_8175.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___323_8175.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___323_8175.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___323_8175.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___323_8175.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___323_8175.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___323_8175.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8178,FStar_Syntax_Syntax.Tm_uvar uu____8179)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8196,uu____8197)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8214,FStar_Syntax_Syntax.Tm_uvar uu____8215)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8232,uu____8233) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7946 with
                     | (rank,tp1) ->
                         let uu____8246 =
                           FStar_All.pipe_right
                             (let uu___324_8250 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___324_8250.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___324_8250.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___324_8250.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___324_8250.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___324_8250.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___324_8250.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___324_8250.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___324_8250.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___324_8250.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8246))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8256 =
            FStar_All.pipe_right
              (let uu___325_8260 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___325_8260.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___325_8260.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___325_8260.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___325_8260.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___325_8260.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___325_8260.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___325_8260.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___325_8260.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___325_8260.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8256)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8321 probs =
      match uu____8321 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8402 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8423 = rank wl.tcenv hd1  in
               (match uu____8423 with
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
                      (let uu____8482 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8486 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8486)
                          in
                       if uu____8482
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
          let uu____8554 = FStar_Syntax_Util.head_and_args t  in
          match uu____8554 with
          | (hd1,uu____8570) ->
              let uu____8591 =
                let uu____8592 = FStar_Syntax_Subst.compress hd1  in
                uu____8592.FStar_Syntax_Syntax.n  in
              (match uu____8591 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8596) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8630  ->
                           match uu____8630 with
                           | (y,uu____8636) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8650  ->
                                       match uu____8650 with
                                       | (x,uu____8656) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8657 -> false)
           in
        let uu____8658 = rank tcenv p  in
        match uu____8658 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8665 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8692 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8706 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8720 -> false
  
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
                        let uu____8772 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8772 with
                        | (k,uu____8778) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8788 -> false)))
            | uu____8789 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8841 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8847 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8847 = (Prims.parse_int "0")))
                           in
                        if uu____8841 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8863 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8869 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8869 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8863)
               in
            let uu____8870 = filter1 u12  in
            let uu____8873 = filter1 u22  in (uu____8870, uu____8873)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8902 = filter_out_common_univs us1 us2  in
                (match uu____8902 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8961 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8961 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8964 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8974 =
                          let uu____8975 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8976 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8975
                            uu____8976
                           in
                        UFailed uu____8974))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9000 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9000 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____9026 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____9026 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____9029 ->
                let uu____9034 =
                  let uu____9035 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____9036 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____9035
                    uu____9036 msg
                   in
                UFailed uu____9034
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9037,uu____9038) ->
              let uu____9039 =
                let uu____9040 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9041 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9040 uu____9041
                 in
              failwith uu____9039
          | (FStar_Syntax_Syntax.U_unknown ,uu____9042) ->
              let uu____9043 =
                let uu____9044 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9045 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9044 uu____9045
                 in
              failwith uu____9043
          | (uu____9046,FStar_Syntax_Syntax.U_bvar uu____9047) ->
              let uu____9048 =
                let uu____9049 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9050 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9049 uu____9050
                 in
              failwith uu____9048
          | (uu____9051,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____9052 =
                let uu____9053 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9054 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9053 uu____9054
                 in
              failwith uu____9052
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9078 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____9078
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____9092 = occurs_univ v1 u3  in
              if uu____9092
              then
                let uu____9093 =
                  let uu____9094 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9095 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9094 uu____9095
                   in
                try_umax_components u11 u21 uu____9093
              else
                (let uu____9097 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9097)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9109 = occurs_univ v1 u3  in
              if uu____9109
              then
                let uu____9110 =
                  let uu____9111 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9112 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9111 uu____9112
                   in
                try_umax_components u11 u21 uu____9110
              else
                (let uu____9114 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9114)
          | (FStar_Syntax_Syntax.U_max uu____9115,uu____9116) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9122 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9122
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9124,FStar_Syntax_Syntax.U_max uu____9125) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9131 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9131
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9133,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9134,FStar_Syntax_Syntax.U_name
             uu____9135) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9136) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9137) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9138,FStar_Syntax_Syntax.U_succ
             uu____9139) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9140,FStar_Syntax_Syntax.U_zero
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
      let uu____9240 = bc1  in
      match uu____9240 with
      | (bs1,mk_cod1) ->
          let uu____9284 = bc2  in
          (match uu____9284 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9395 = aux xs ys  in
                     (match uu____9395 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9478 =
                       let uu____9485 = mk_cod1 xs  in ([], uu____9485)  in
                     let uu____9488 =
                       let uu____9495 = mk_cod2 ys  in ([], uu____9495)  in
                     (uu____9478, uu____9488)
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
                  let uu____9563 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9563 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9566 =
                    let uu____9567 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9567 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9566
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9572 = has_type_guard t1 t2  in (uu____9572, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9573 = has_type_guard t2 t1  in (uu____9573, wl)
  
let is_flex_pat :
  'Auu____9582 'Auu____9583 'Auu____9584 .
    ('Auu____9582,'Auu____9583,'Auu____9584 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___297_9597  ->
    match uu___297_9597 with
    | (uu____9606,uu____9607,[]) -> true
    | uu____9610 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9641 = f  in
      match uu____9641 with
      | (uu____9648,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9649;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9650;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9653;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9654;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9655;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9707  ->
                 match uu____9707 with
                 | (y,uu____9713) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9835 =
                  let uu____9848 =
                    let uu____9851 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9851  in
                  ((FStar_List.rev pat_binders), uu____9848)  in
                FStar_Pervasives_Native.Some uu____9835
            | (uu____9878,[]) ->
                let uu____9901 =
                  let uu____9914 =
                    let uu____9917 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9917  in
                  ((FStar_List.rev pat_binders), uu____9914)  in
                FStar_Pervasives_Native.Some uu____9901
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9982 =
                  let uu____9983 = FStar_Syntax_Subst.compress a  in
                  uu____9983.FStar_Syntax_Syntax.n  in
                (match uu____9982 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10001 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____10001
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___326_10022 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___326_10022.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___326_10022.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____10026 =
                            let uu____10027 =
                              let uu____10034 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____10034)  in
                            FStar_Syntax_Syntax.NT uu____10027  in
                          [uu____10026]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___327_10046 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___327_10046.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___327_10046.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10047 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____10075 =
                  let uu____10088 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10088  in
                (match uu____10075 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10151 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10178 ->
               let uu____10179 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10179 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10455 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10455
       then
         let uu____10456 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10456
       else ());
      (let uu____10458 = next_prob probs  in
       match uu____10458 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___328_10485 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___328_10485.wl_deferred);
               ctr = (uu___328_10485.ctr);
               defer_ok = (uu___328_10485.defer_ok);
               smt_ok = (uu___328_10485.smt_ok);
               tcenv = (uu___328_10485.tcenv);
               wl_implicits = (uu___328_10485.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10493 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10493
                 then
                   let uu____10494 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10494
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
                           (let uu___329_10499 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___329_10499.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___329_10499.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___329_10499.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___329_10499.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___329_10499.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___329_10499.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___329_10499.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___329_10499.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___329_10499.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10521 ->
                let uu____10530 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10589  ->
                          match uu____10589 with
                          | (c,uu____10597,uu____10598) -> c < probs.ctr))
                   in
                (match uu____10530 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10639 =
                            let uu____10644 =
                              FStar_List.map
                                (fun uu____10659  ->
                                   match uu____10659 with
                                   | (uu____10670,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10644, (probs.wl_implicits))  in
                          Success uu____10639
                      | uu____10673 ->
                          let uu____10682 =
                            let uu___330_10683 = probs  in
                            let uu____10684 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10703  ->
                                      match uu____10703 with
                                      | (uu____10710,uu____10711,y) -> y))
                               in
                            {
                              attempting = uu____10684;
                              wl_deferred = rest;
                              ctr = (uu___330_10683.ctr);
                              defer_ok = (uu___330_10683.defer_ok);
                              smt_ok = (uu___330_10683.smt_ok);
                              tcenv = (uu___330_10683.tcenv);
                              wl_implicits = (uu___330_10683.wl_implicits)
                            }  in
                          solve env uu____10682))))

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
            let uu____10718 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10718 with
            | USolved wl1 ->
                let uu____10720 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10720
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
                  let uu____10772 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10772 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10775 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10787;
                  FStar_Syntax_Syntax.vars = uu____10788;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10791;
                  FStar_Syntax_Syntax.vars = uu____10792;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10804,uu____10805) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10812,FStar_Syntax_Syntax.Tm_uinst uu____10813) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10820 -> USolved wl

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
            ((let uu____10830 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10830
              then
                let uu____10831 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10831 msg
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
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____10917 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10917 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10970 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10970
                then
                  let uu____10971 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10972 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10971 uu____10972
                else ());
               (let uu____10974 = head_matches_delta env1 () t1 t2  in
                match uu____10974 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____11019 = eq_prob t1 t2 wl2  in
                         (match uu____11019 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11040 ->
                         let uu____11049 = eq_prob t1 t2 wl2  in
                         (match uu____11049 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11098 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11113 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11114 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11113, uu____11114)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11119 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11120 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11119, uu____11120)
                            in
                         (match uu____11098 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11151 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11151 with
                                | (t1_hd,t1_args) ->
                                    let uu____11190 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11190 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11244 =
                                              let uu____11251 =
                                                let uu____11260 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11260 :: t1_args  in
                                              let uu____11273 =
                                                let uu____11280 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11280 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11321  ->
                                                   fun uu____11322  ->
                                                     fun uu____11323  ->
                                                       match (uu____11321,
                                                               uu____11322,
                                                               uu____11323)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11365),
                                                          (a2,uu____11367))
                                                           ->
                                                           let uu____11392 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11392
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11251
                                                uu____11273
                                               in
                                            match uu____11244 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___331_11418 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___331_11418.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___331_11418.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11434 =
                                                  solve env1 wl'  in
                                                (match uu____11434 with
                                                 | Success (uu____11437,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___332_11441
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___332_11441.attempting);
                                                            wl_deferred =
                                                              (uu___332_11441.wl_deferred);
                                                            ctr =
                                                              (uu___332_11441.ctr);
                                                            defer_ok =
                                                              (uu___332_11441.defer_ok);
                                                            smt_ok =
                                                              (uu___332_11441.smt_ok);
                                                            tcenv =
                                                              (uu___332_11441.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11450 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11482 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11482 with
                                | (t1_base,p1_opt) ->
                                    let uu____11529 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11529 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11639 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11639
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t
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
                                               let uu____11687 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11687
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
                                               let uu____11717 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11717
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
                                               let uu____11747 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11747
                                           | uu____11750 -> t_base  in
                                         let uu____11767 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11767 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11781 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11781, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11788 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11788 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11835 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11835 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11882 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11882
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
                              let uu____11906 = combine t11 t21 wl2  in
                              (match uu____11906 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11939 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11939
                                     then
                                       let uu____11940 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11940
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11979 ts1 =
               match uu____11979 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12042 = pairwise out t wl2  in
                        (match uu____12042 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12078 =
               let uu____12089 = FStar_List.hd ts  in (uu____12089, [], wl1)
                in
             let uu____12098 = FStar_List.tl ts  in
             aux uu____12078 uu____12098  in
           let uu____12105 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12105 with
           | (this_flex,this_rigid) ->
               let uu____12129 =
                 let uu____12130 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12130.FStar_Syntax_Syntax.n  in
               (match uu____12129 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12151 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12151
                    then
                      let uu____12152 = destruct_flex_t this_flex wl  in
                      (match uu____12152 with
                       | (flex,wl1) ->
                           let uu____12159 = quasi_pattern env flex  in
                           (match uu____12159 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12177 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12177
                                  then
                                    let uu____12178 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12178
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12181 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___333_12184 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___333_12184.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___333_12184.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___333_12184.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___333_12184.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___333_12184.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___333_12184.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___333_12184.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___333_12184.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___333_12184.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12181)
                | uu____12185 ->
                    ((let uu____12187 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12187
                      then
                        let uu____12188 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12188
                      else ());
                     (let uu____12190 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12190 with
                      | (u,_args) ->
                          let uu____12227 =
                            let uu____12228 = FStar_Syntax_Subst.compress u
                               in
                            uu____12228.FStar_Syntax_Syntax.n  in
                          (match uu____12227 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12259 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12259 with
                                 | (u',uu____12275) ->
                                     let uu____12296 =
                                       let uu____12297 = whnf env u'  in
                                       uu____12297.FStar_Syntax_Syntax.n  in
                                     (match uu____12296 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12322 -> false)
                                  in
                               let uu____12323 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___298_12346  ->
                                         match uu___298_12346 with
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
                                              | uu____12355 -> false)
                                         | uu____12358 -> false))
                                  in
                               (match uu____12323 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12372 = whnf env this_rigid
                                         in
                                      let uu____12373 =
                                        FStar_List.collect
                                          (fun uu___299_12379  ->
                                             match uu___299_12379 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12385 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12385]
                                             | uu____12387 -> [])
                                          bounds_probs
                                         in
                                      uu____12372 :: uu____12373  in
                                    let uu____12388 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12388 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12419 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12434 =
                                               let uu____12435 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12435.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12434 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12447 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12447)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12456 -> bound  in
                                           let uu____12457 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12457)  in
                                         (match uu____12419 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12486 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12486
                                                then
                                                  let wl'1 =
                                                    let uu___334_12488 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___334_12488.wl_deferred);
                                                      ctr =
                                                        (uu___334_12488.ctr);
                                                      defer_ok =
                                                        (uu___334_12488.defer_ok);
                                                      smt_ok =
                                                        (uu___334_12488.smt_ok);
                                                      tcenv =
                                                        (uu___334_12488.tcenv);
                                                      wl_implicits =
                                                        (uu___334_12488.wl_implicits)
                                                    }  in
                                                  let uu____12489 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12489
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12492 =
                                                  solve_t env eq_prob
                                                    (let uu___335_12494 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___335_12494.wl_deferred);
                                                       ctr =
                                                         (uu___335_12494.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___335_12494.smt_ok);
                                                       tcenv =
                                                         (uu___335_12494.tcenv);
                                                       wl_implicits =
                                                         (uu___335_12494.wl_implicits)
                                                     })
                                                   in
                                                match uu____12492 with
                                                | Success uu____12495 ->
                                                    let wl2 =
                                                      let uu___336_12501 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___336_12501.wl_deferred);
                                                        ctr =
                                                          (uu___336_12501.ctr);
                                                        defer_ok =
                                                          (uu___336_12501.defer_ok);
                                                        smt_ok =
                                                          (uu___336_12501.smt_ok);
                                                        tcenv =
                                                          (uu___336_12501.tcenv);
                                                        wl_implicits =
                                                          (uu___336_12501.wl_implicits)
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
                                                    let uu____12516 =
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
                                                     (let uu____12528 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12528
                                                      then
                                                        let uu____12529 =
                                                          let uu____12530 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12530
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12529
                                                      else ());
                                                     (let uu____12536 =
                                                        let uu____12551 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12551)
                                                         in
                                                      match uu____12536 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12573))
                                                          ->
                                                          let uu____12598 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12598
                                                           with
                                                           | (eq_prob1,wl2)
                                                               ->
                                                               (def_check_prob
                                                                  "meet_or_join3"
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                (let wl3 =
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
                                                                 let uu____12615
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12615)))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          let uu____12639 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12639
                                                           with
                                                           | (eq_prob1,wl2)
                                                               ->
                                                               (def_check_prob
                                                                  "meet_or_join4"
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                (let phi1 =
                                                                   guard_on_element
                                                                    wl2 tp x
                                                                    phi
                                                                    in
                                                                 let wl3 =
                                                                   let uu____12657
                                                                    =
                                                                    let uu____12662
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12662
                                                                     in
                                                                   solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12657
                                                                    [] wl2
                                                                    in
                                                                 let uu____12667
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12667)))
                                                      | uu____12668 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12683 when flip ->
                               let uu____12684 =
                                 let uu____12685 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12686 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12685 uu____12686
                                  in
                               failwith uu____12684
                           | uu____12687 ->
                               let uu____12688 =
                                 let uu____12689 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12690 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12689 uu____12690
                                  in
                               failwith uu____12688)))))

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
                      (fun uu____12718  ->
                         match uu____12718 with
                         | (x,i) ->
                             let uu____12729 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12729, i)) bs_lhs
                     in
                  let uu____12730 = lhs  in
                  match uu____12730 with
                  | (uu____12731,u_lhs,uu____12733) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12826 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12836 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12836, univ)
                             in
                          match uu____12826 with
                          | (k,univ) ->
                              let uu____12843 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12843 with
                               | (uu____12858,u,wl3) ->
                                   let uu____12861 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12861, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12887 =
                              let uu____12898 =
                                let uu____12907 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12907 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12950  ->
                                   fun uu____12951  ->
                                     match (uu____12950, uu____12951) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13030 =
                                           let uu____13037 =
                                             let uu____13040 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13040
                                              in
                                           copy_uvar u_lhs [] uu____13037 wl2
                                            in
                                         (match uu____13030 with
                                          | (uu____13065,t_a,wl3) ->
                                              let uu____13068 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13068 with
                                               | (uu____13085,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12898
                                ([], wl1)
                               in
                            (match uu____12887 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___337_13127 = ct  in
                                   let uu____13128 =
                                     let uu____13131 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13131
                                      in
                                   let uu____13140 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___337_13127.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___337_13127.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13128;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13140;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___337_13127.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___338_13154 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___338_13154.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___338_13154.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13157 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13157 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13211 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13211 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13222 =
                                          let uu____13227 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13227)  in
                                        TERM uu____13222  in
                                      let uu____13228 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13228 with
                                       | (sub_prob,wl3) ->
                                           let uu____13239 =
                                             let uu____13240 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13240
                                              in
                                           solve env uu____13239))
                             | (x,imp)::formals2 ->
                                 let uu____13254 =
                                   let uu____13261 =
                                     let uu____13264 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13264
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13261 wl1
                                    in
                                 (match uu____13254 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13283 =
                                          let uu____13286 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13286
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13283 u_x
                                         in
                                      let uu____13287 =
                                        let uu____13290 =
                                          let uu____13293 =
                                            let uu____13294 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13294, imp)  in
                                          [uu____13293]  in
                                        FStar_List.append bs_terms
                                          uu____13290
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13287 formals2 wl2)
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
              (let uu____13336 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13336
               then
                 let uu____13337 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13338 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13337 (rel_to_string (p_rel orig)) uu____13338
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13443 = rhs wl1 scope env1 subst1  in
                     (match uu____13443 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13463 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13463
                            then
                              let uu____13464 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13464
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___339_13518 = hd1  in
                       let uu____13519 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___339_13518.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___339_13518.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13519
                       }  in
                     let hd21 =
                       let uu___340_13523 = hd2  in
                       let uu____13524 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___340_13523.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___340_13523.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13524
                       }  in
                     let uu____13527 =
                       let uu____13532 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13532
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13527 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13551 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13551
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13555 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13555 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13610 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13610
                                  in
                               ((let uu____13622 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13622
                                 then
                                   let uu____13623 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13624 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13623
                                     uu____13624
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13651 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13680 = aux wl [] env [] bs1 bs2  in
               match uu____13680 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13727 = attempt sub_probs wl2  in
                   solve env uu____13727)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13732 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13732 wl)

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
              let uu____13746 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13746 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13776 = lhs1  in
              match uu____13776 with
              | (uu____13779,ctx_u,uu____13781) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13787 ->
                        let uu____13788 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13788 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13835 = quasi_pattern env1 lhs1  in
              match uu____13835 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13865) ->
                  let uu____13870 = lhs1  in
                  (match uu____13870 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13884 = occurs_check ctx_u rhs1  in
                       (match uu____13884 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13926 =
                                let uu____13933 =
                                  let uu____13934 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13934
                                   in
                                FStar_Util.Inl uu____13933  in
                              (uu____13926, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13954 =
                                 let uu____13955 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13955  in
                               if uu____13954
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13975 =
                                    let uu____13982 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13982  in
                                  let uu____13987 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13975, uu____13987)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14049  ->
                     match uu____14049 with
                     | (x,i) ->
                         let uu____14060 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14060, i)) bs_lhs
                 in
              let uu____14061 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14061 with
              | (rhs_hd,args) ->
                  let uu____14098 = FStar_Util.prefix args  in
                  (match uu____14098 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14156 = lhs1  in
                       (match uu____14156 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14160 =
                              let uu____14171 =
                                let uu____14178 =
                                  let uu____14181 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14181
                                   in
                                copy_uvar u_lhs [] uu____14178 wl1  in
                              match uu____14171 with
                              | (uu____14206,t_last_arg,wl2) ->
                                  let uu____14209 =
                                    let uu____14216 =
                                      let uu____14217 =
                                        let uu____14224 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14224]  in
                                      FStar_List.append bs_lhs uu____14217
                                       in
                                    copy_uvar u_lhs uu____14216 t_res_lhs wl2
                                     in
                                  (match uu____14209 with
                                   | (uu____14251,lhs',wl3) ->
                                       let uu____14254 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14254 with
                                        | (uu____14271,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14160 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14292 =
                                     let uu____14293 =
                                       let uu____14298 =
                                         let uu____14299 =
                                           let uu____14302 =
                                             let uu____14307 =
                                               let uu____14308 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14308]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14307
                                              in
                                           uu____14302
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14299
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14298)  in
                                     TERM uu____14293  in
                                   [uu____14292]  in
                                 let uu____14329 =
                                   let uu____14336 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14336 with
                                   | (p1,wl3) ->
                                       let uu____14353 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14353 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14329 with
                                  | (sub_probs,wl3) ->
                                      let uu____14380 =
                                        let uu____14381 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14381  in
                                      solve env1 uu____14380))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14414 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14414 with
                | (uu____14429,args) ->
                    (match args with | [] -> false | uu____14457 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14472 =
                  let uu____14473 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14473.FStar_Syntax_Syntax.n  in
                match uu____14472 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14476 -> true
                | uu____14489 -> false  in
              let uu____14490 = quasi_pattern env1 lhs1  in
              match uu____14490 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14501 =
                    let uu____14502 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14502
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14501
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14509 = is_app rhs1  in
                  if uu____14509
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14511 = is_arrow rhs1  in
                     if uu____14511
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14513 =
                          let uu____14514 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14514
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14513))
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
                let uu____14517 = lhs  in
                (match uu____14517 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14521 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14521 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14536 =
                              let uu____14539 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14539
                               in
                            FStar_All.pipe_right uu____14536
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14554 = occurs_check ctx_uv rhs1  in
                          (match uu____14554 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14576 =
                                   let uu____14577 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14577
                                    in
                                 giveup_or_defer env orig wl uu____14576
                               else
                                 (let uu____14579 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14579
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14584 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14584
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14586 =
                                         let uu____14587 =
                                           names_to_string1 fvs2  in
                                         let uu____14588 =
                                           names_to_string1 fvs1  in
                                         let uu____14589 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14587 uu____14588
                                           uu____14589
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14586)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14595 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14599 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14599 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14622 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14622
                             | (FStar_Util.Inl msg,uu____14624) ->
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
                  (let uu____14653 =
                     let uu____14670 = quasi_pattern env lhs  in
                     let uu____14677 = quasi_pattern env rhs  in
                     (uu____14670, uu____14677)  in
                   match uu____14653 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14720 = lhs  in
                       (match uu____14720 with
                        | ({ FStar_Syntax_Syntax.n = uu____14721;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14723;_},u_lhs,uu____14725)
                            ->
                            let uu____14728 = rhs  in
                            (match uu____14728 with
                             | (uu____14729,u_rhs,uu____14731) ->
                                 let uu____14732 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14732
                                 then
                                   let uu____14733 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14733
                                 else
                                   (let uu____14735 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14735 with
                                    | (sub_prob,wl1) ->
                                        let uu____14746 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14746 with
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
                                             let uu____14774 =
                                               let uu____14781 =
                                                 let uu____14784 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14784
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
                                                 uu____14781
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14774 with
                                              | (uu____14787,w,wl2) ->
                                                  let w_app =
                                                    let uu____14793 =
                                                      let uu____14798 =
                                                        FStar_List.map
                                                          (fun uu____14807 
                                                             ->
                                                             match uu____14807
                                                             with
                                                             | (z,uu____14813)
                                                                 ->
                                                                 let uu____14814
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14814)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14798
                                                       in
                                                    uu____14793
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14818 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14818
                                                    then
                                                      let uu____14819 =
                                                        let uu____14822 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14823 =
                                                          let uu____14826 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14827 =
                                                            let uu____14830 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14831 =
                                                              let uu____14834
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14839
                                                                =
                                                                let uu____14842
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14847
                                                                  =
                                                                  let uu____14850
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14850]
                                                                   in
                                                                uu____14842
                                                                  ::
                                                                  uu____14847
                                                                 in
                                                              uu____14834 ::
                                                                uu____14839
                                                               in
                                                            uu____14830 ::
                                                              uu____14831
                                                             in
                                                          uu____14826 ::
                                                            uu____14827
                                                           in
                                                        uu____14822 ::
                                                          uu____14823
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14819
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14856 =
                                                          let uu____14861 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14861)
                                                           in
                                                        TERM uu____14856  in
                                                      let uu____14862 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14862
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14867 =
                                                             let uu____14872
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
                                                               uu____14872)
                                                              in
                                                           TERM uu____14867
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14873 =
                                                      let uu____14874 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14874
                                                       in
                                                    solve env uu____14873)))))))
                   | uu____14875 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14939 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14939
            then
              let uu____14940 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14941 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14942 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14943 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14940 uu____14941 uu____14942 uu____14943
            else ());
           (let uu____14947 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14947
            then
              let uu____14948 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14949 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14950 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14951 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14948 uu____14949 uu____14950 uu____14951
            else ());
           (let uu____14953 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14953 with
            | (head1,args1) ->
                let uu____14990 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14990 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15044 =
                         let uu____15045 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15046 = args_to_string args1  in
                         let uu____15047 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15048 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15045 uu____15046 uu____15047 uu____15048
                          in
                       giveup env1 uu____15044 orig
                     else
                       (let uu____15050 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15056 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15056 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15050
                        then
                          let uu____15057 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____15057 with
                          | USolved wl2 ->
                              let uu____15059 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____15059
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____15063 = base_and_refinement env1 t1  in
                           match uu____15063 with
                           | (base1,refinement1) ->
                               let uu____15088 = base_and_refinement env1 t2
                                  in
                               (match uu____15088 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15145 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15145 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15149 =
                                                FStar_List.fold_right2
                                                  (fun uu____15182  ->
                                                     fun uu____15183  ->
                                                       fun uu____15184  ->
                                                         match (uu____15182,
                                                                 uu____15183,
                                                                 uu____15184)
                                                         with
                                                         | ((a,uu____15220),
                                                            (a',uu____15222),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15243
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15243
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15149 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15271 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15271
                                                     then
                                                       let uu____15272 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15272
                                                     else ());
                                                    FStar_List.iter
                                                      (def_check_prob
                                                         "solve_t' subprobs")
                                                      subprobs;
                                                    (let formula =
                                                       let uu____15278 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15278
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     let uu____15286 =
                                                       attempt subprobs wl4
                                                        in
                                                     solve env1 uu____15286))))
                                     | uu____15287 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___341_15327 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___341_15327.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___341_15327.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___341_15327.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___341_15327.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___341_15327.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___341_15327.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___341_15327.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___341_15327.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15365 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15365
            then
              let uu____15366 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15367 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15368 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15369 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15366 uu____15367 uu____15368 uu____15369
            else ());
           (let uu____15371 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15371 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15402,uu____15403) ->
                     let rec may_relate head3 =
                       let uu____15430 =
                         let uu____15431 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15431.FStar_Syntax_Syntax.n  in
                       match uu____15430 with
                       | FStar_Syntax_Syntax.Tm_name uu____15434 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15435 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15458;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15459;
                             FStar_Syntax_Syntax.fv_qual = uu____15460;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15463;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15464;
                             FStar_Syntax_Syntax.fv_qual = uu____15465;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15469,uu____15470) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15512) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15518) ->
                           may_relate t
                       | uu____15523 -> false  in
                     let uu____15524 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15524
                     then
                       let uu____15525 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15525 with
                        | (guard,wl2) ->
                            let uu____15532 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15532)
                     else
                       (let uu____15534 =
                          let uu____15535 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15536 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15535 uu____15536
                           in
                        giveup env1 uu____15534 orig)
                 | (HeadMatch (true ),uu____15537) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____15550 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15550 with
                        | (guard,wl2) ->
                            let uu____15557 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15557)
                     else
                       (let uu____15559 =
                          let uu____15560 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____15561 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____15560 uu____15561
                           in
                        giveup env1 uu____15559 orig)
                 | (uu____15562,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___342_15576 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___342_15576.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___342_15576.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___342_15576.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___342_15576.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___342_15576.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___342_15576.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___342_15576.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___342_15576.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15600 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15600
          then
            let uu____15601 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15601
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15606 =
                let uu____15609 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15609  in
              def_check_closed_in (p_loc orig) "ref.t1" uu____15606 t1);
             (let uu____15621 =
                let uu____15624 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15624  in
              def_check_closed_in (p_loc orig) "ref.t2" uu____15621 t2);
             (let uu____15636 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15636
              then
                let uu____15637 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15638 =
                  let uu____15639 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15640 =
                    let uu____15641 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15641  in
                  Prims.strcat uu____15639 uu____15640  in
                let uu____15642 =
                  let uu____15643 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15644 =
                    let uu____15645 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15645  in
                  Prims.strcat uu____15643 uu____15644  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15637
                  uu____15638 uu____15642
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15648,uu____15649) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15674,FStar_Syntax_Syntax.Tm_delayed uu____15675) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15700,uu____15701) ->
                  let uu____15728 =
                    let uu___343_15729 = problem  in
                    let uu____15730 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___343_15729.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15730;
                      FStar_TypeChecker_Common.relation =
                        (uu___343_15729.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___343_15729.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___343_15729.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___343_15729.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___343_15729.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___343_15729.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___343_15729.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___343_15729.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15728 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15731,uu____15732) ->
                  let uu____15739 =
                    let uu___344_15740 = problem  in
                    let uu____15741 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___344_15740.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15741;
                      FStar_TypeChecker_Common.relation =
                        (uu___344_15740.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___344_15740.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___344_15740.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___344_15740.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___344_15740.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___344_15740.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___344_15740.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___344_15740.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15739 wl
              | (uu____15742,FStar_Syntax_Syntax.Tm_ascribed uu____15743) ->
                  let uu____15770 =
                    let uu___345_15771 = problem  in
                    let uu____15772 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___345_15771.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___345_15771.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___345_15771.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15772;
                      FStar_TypeChecker_Common.element =
                        (uu___345_15771.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___345_15771.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___345_15771.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___345_15771.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___345_15771.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___345_15771.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15770 wl
              | (uu____15773,FStar_Syntax_Syntax.Tm_meta uu____15774) ->
                  let uu____15781 =
                    let uu___346_15782 = problem  in
                    let uu____15783 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___346_15782.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___346_15782.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___346_15782.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15783;
                      FStar_TypeChecker_Common.element =
                        (uu___346_15782.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___346_15782.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___346_15782.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___346_15782.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___346_15782.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___346_15782.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15781 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15785),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15787)) ->
                  let uu____15796 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15796
              | (FStar_Syntax_Syntax.Tm_bvar uu____15797,uu____15798) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15799,FStar_Syntax_Syntax.Tm_bvar uu____15800) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___300_15859 =
                    match uu___300_15859 with
                    | [] -> c
                    | bs ->
                        let uu____15881 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15881
                     in
                  let uu____15890 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15890 with
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
                                    let uu____16013 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____16013
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
                  let mk_t t l uu___301_16088 =
                    match uu___301_16088 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____16122 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____16122 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16241 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16242 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16241
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16242 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16243,uu____16244) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16271 -> true
                    | uu____16288 -> false  in
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
                      (let uu____16341 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___347_16349 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___347_16349.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___347_16349.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___347_16349.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___347_16349.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___347_16349.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___347_16349.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___347_16349.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___347_16349.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___347_16349.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___347_16349.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___347_16349.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___347_16349.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___347_16349.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___347_16349.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___347_16349.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___347_16349.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___347_16349.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___347_16349.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___347_16349.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___347_16349.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___347_16349.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___347_16349.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___347_16349.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___347_16349.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___347_16349.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___347_16349.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___347_16349.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___347_16349.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___347_16349.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___347_16349.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___347_16349.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___347_16349.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___347_16349.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___347_16349.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___347_16349.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___347_16349.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16341 with
                       | (uu____16352,ty,uu____16354) ->
                           let uu____16355 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16355)
                     in
                  let uu____16356 =
                    let uu____16373 = maybe_eta t1  in
                    let uu____16380 = maybe_eta t2  in
                    (uu____16373, uu____16380)  in
                  (match uu____16356 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___348_16422 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___348_16422.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___348_16422.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___348_16422.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___348_16422.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___348_16422.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___348_16422.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___348_16422.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___348_16422.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16443 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16443
                       then
                         let uu____16444 = destruct_flex_t not_abs wl  in
                         (match uu____16444 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16459 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16459.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16459.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16459.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16459.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16459.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16459.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16459.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16459.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16481 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16481
                       then
                         let uu____16482 = destruct_flex_t not_abs wl  in
                         (match uu____16482 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16497 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16497.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16497.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16497.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16497.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16497.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16497.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16497.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16497.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16499 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16516,FStar_Syntax_Syntax.Tm_abs uu____16517) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16544 -> true
                    | uu____16561 -> false  in
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
                      (let uu____16614 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___347_16622 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___347_16622.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___347_16622.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___347_16622.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___347_16622.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___347_16622.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___347_16622.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___347_16622.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___347_16622.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___347_16622.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___347_16622.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___347_16622.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___347_16622.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___347_16622.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___347_16622.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___347_16622.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___347_16622.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___347_16622.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___347_16622.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___347_16622.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___347_16622.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___347_16622.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___347_16622.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___347_16622.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___347_16622.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___347_16622.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___347_16622.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___347_16622.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___347_16622.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___347_16622.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___347_16622.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___347_16622.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___347_16622.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___347_16622.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___347_16622.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___347_16622.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___347_16622.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16614 with
                       | (uu____16625,ty,uu____16627) ->
                           let uu____16628 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16628)
                     in
                  let uu____16629 =
                    let uu____16646 = maybe_eta t1  in
                    let uu____16653 = maybe_eta t2  in
                    (uu____16646, uu____16653)  in
                  (match uu____16629 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___348_16695 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___348_16695.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___348_16695.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___348_16695.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___348_16695.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___348_16695.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___348_16695.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___348_16695.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___348_16695.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16716 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16716
                       then
                         let uu____16717 = destruct_flex_t not_abs wl  in
                         (match uu____16717 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16732 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16732.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16732.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16732.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16732.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16732.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16732.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16732.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16732.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16754 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16754
                       then
                         let uu____16755 = destruct_flex_t not_abs wl  in
                         (match uu____16755 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16770 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16770.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16770.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16770.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16770.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16770.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16770.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16770.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16770.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16772 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16804 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16804) &&
                       (let uu____16808 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16808))
                      &&
                      (let uu____16815 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16815 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___302_16827 =
                             match uu___302_16827 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16828 -> true
                             | uu____16829 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16830 -> false)
                     in
                  let uu____16831 = as_refinement should_delta env wl t1  in
                  (match uu____16831 with
                   | (x11,phi1) ->
                       let uu____16844 = as_refinement should_delta env wl t2
                          in
                       (match uu____16844 with
                        | (x21,phi21) ->
                            let uu____16857 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16857 with
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
                                   let uu____16923 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16923
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16935 =
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
                                   (let uu____16946 =
                                      let uu____16949 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16949
                                       in
                                    def_check_closed_in (p_loc orig) "ref.1"
                                      uu____16946 (p_guard base_prob));
                                   (let uu____16961 =
                                      let uu____16964 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16964
                                       in
                                    def_check_closed_in (p_loc orig) "ref.2"
                                      uu____16961 impl);
                                   (let wl2 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl1
                                       in
                                    let uu____16976 = attempt [base_prob] wl2
                                       in
                                    solve env1 uu____16976)
                                    in
                                 let has_uvars =
                                   (let uu____16980 =
                                      let uu____16981 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16981  in
                                    Prims.op_Negation uu____16980) ||
                                     (let uu____16985 =
                                        let uu____16986 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16986
                                         in
                                      Prims.op_Negation uu____16985)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16989 =
                                     let uu____16994 =
                                       let uu____17001 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____17001]  in
                                     mk_t_problem wl1 uu____16994 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16989 with
                                    | (ref_prob,wl2) ->
                                        let uu____17016 =
                                          solve env1
                                            (let uu___350_17018 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___350_17018.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___350_17018.smt_ok);
                                               tcenv = (uu___350_17018.tcenv);
                                               wl_implicits =
                                                 (uu___350_17018.wl_implicits)
                                             })
                                           in
                                        (match uu____17016 with
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
                                         | Success uu____17028 ->
                                             let guard =
                                               let uu____17036 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____17036
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___351_17045 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___351_17045.attempting);
                                                 wl_deferred =
                                                   (uu___351_17045.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___351_17045.defer_ok);
                                                 smt_ok =
                                                   (uu___351_17045.smt_ok);
                                                 tcenv =
                                                   (uu___351_17045.tcenv);
                                                 wl_implicits =
                                                   (uu___351_17045.wl_implicits)
                                               }  in
                                             let uu____17046 =
                                               attempt [base_prob] wl4  in
                                             solve env1 uu____17046))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17048,FStar_Syntax_Syntax.Tm_uvar uu____17049) ->
                  let uu____17078 = destruct_flex_t t1 wl  in
                  (match uu____17078 with
                   | (f1,wl1) ->
                       let uu____17085 = destruct_flex_t t2 wl1  in
                       (match uu____17085 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17092;
                    FStar_Syntax_Syntax.pos = uu____17093;
                    FStar_Syntax_Syntax.vars = uu____17094;_},uu____17095),FStar_Syntax_Syntax.Tm_uvar
                 uu____17096) ->
                  let uu____17145 = destruct_flex_t t1 wl  in
                  (match uu____17145 with
                   | (f1,wl1) ->
                       let uu____17152 = destruct_flex_t t2 wl1  in
                       (match uu____17152 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17159,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17160;
                    FStar_Syntax_Syntax.pos = uu____17161;
                    FStar_Syntax_Syntax.vars = uu____17162;_},uu____17163))
                  ->
                  let uu____17212 = destruct_flex_t t1 wl  in
                  (match uu____17212 with
                   | (f1,wl1) ->
                       let uu____17219 = destruct_flex_t t2 wl1  in
                       (match uu____17219 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17226;
                    FStar_Syntax_Syntax.pos = uu____17227;
                    FStar_Syntax_Syntax.vars = uu____17228;_},uu____17229),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17230;
                    FStar_Syntax_Syntax.pos = uu____17231;
                    FStar_Syntax_Syntax.vars = uu____17232;_},uu____17233))
                  ->
                  let uu____17302 = destruct_flex_t t1 wl  in
                  (match uu____17302 with
                   | (f1,wl1) ->
                       let uu____17309 = destruct_flex_t t2 wl1  in
                       (match uu____17309 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____17316,uu____17317) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17332 = destruct_flex_t t1 wl  in
                  (match uu____17332 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17339;
                    FStar_Syntax_Syntax.pos = uu____17340;
                    FStar_Syntax_Syntax.vars = uu____17341;_},uu____17342),uu____17343)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17378 = destruct_flex_t t1 wl  in
                  (match uu____17378 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17385,FStar_Syntax_Syntax.Tm_uvar uu____17386) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17401,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17402;
                    FStar_Syntax_Syntax.pos = uu____17403;
                    FStar_Syntax_Syntax.vars = uu____17404;_},uu____17405))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17440,FStar_Syntax_Syntax.Tm_arrow uu____17441) ->
                  solve_t' env
                    (let uu___352_17469 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___352_17469.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___352_17469.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___352_17469.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___352_17469.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___352_17469.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___352_17469.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___352_17469.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___352_17469.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___352_17469.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17470;
                    FStar_Syntax_Syntax.pos = uu____17471;
                    FStar_Syntax_Syntax.vars = uu____17472;_},uu____17473),FStar_Syntax_Syntax.Tm_arrow
                 uu____17474) ->
                  solve_t' env
                    (let uu___352_17522 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___352_17522.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___352_17522.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___352_17522.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___352_17522.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___352_17522.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___352_17522.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___352_17522.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___352_17522.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___352_17522.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17523,FStar_Syntax_Syntax.Tm_uvar uu____17524) ->
                  let uu____17539 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17539
              | (uu____17540,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17541;
                    FStar_Syntax_Syntax.pos = uu____17542;
                    FStar_Syntax_Syntax.vars = uu____17543;_},uu____17544))
                  ->
                  let uu____17579 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17579
              | (FStar_Syntax_Syntax.Tm_uvar uu____17580,uu____17581) ->
                  let uu____17596 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17596
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17597;
                    FStar_Syntax_Syntax.pos = uu____17598;
                    FStar_Syntax_Syntax.vars = uu____17599;_},uu____17600),uu____17601)
                  ->
                  let uu____17636 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17636
              | (FStar_Syntax_Syntax.Tm_refine uu____17637,uu____17638) ->
                  let t21 =
                    let uu____17646 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17646  in
                  solve_t env
                    (let uu___353_17672 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___353_17672.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___353_17672.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___353_17672.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___353_17672.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___353_17672.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___353_17672.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___353_17672.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___353_17672.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___353_17672.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17673,FStar_Syntax_Syntax.Tm_refine uu____17674) ->
                  let t11 =
                    let uu____17682 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17682  in
                  solve_t env
                    (let uu___354_17708 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___354_17708.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___354_17708.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___354_17708.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___354_17708.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___354_17708.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___354_17708.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___354_17708.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___354_17708.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___354_17708.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17790 =
                    let uu____17791 = guard_of_prob env wl problem t1 t2  in
                    match uu____17791 with
                    | (guard,wl1) ->
                        let uu____17798 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17798
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____18009 = br1  in
                        (match uu____18009 with
                         | (p1,w1,uu____18034) ->
                             let uu____18051 = br2  in
                             (match uu____18051 with
                              | (p2,w2,uu____18070) ->
                                  let uu____18075 =
                                    let uu____18076 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____18076  in
                                  if uu____18075
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____18092 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____18092 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____18125 = br2  in
                                         (match uu____18125 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____18160 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____18160
                                                 in
                                              let uu____18171 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____18194,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____18211) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____18254 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____18254 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____18171
                                                (fun uu____18296  ->
                                                   match uu____18296 with
                                                   | (wprobs,wl2) ->
                                                       let uu____18317 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____18317
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____18332 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____18332
                                                              (fun
                                                                 uu____18356 
                                                                 ->
                                                                 match uu____18356
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18441 -> FStar_Pervasives_Native.None  in
                  let uu____18478 = solve_branches wl brs1 brs2  in
                  (match uu____18478 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18506 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18506 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18523 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18523  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18532 =
                              let uu____18533 =
                                attempt sub_probs1
                                  (let uu___355_18535 = wl3  in
                                   {
                                     attempting = (uu___355_18535.attempting);
                                     wl_deferred =
                                       (uu___355_18535.wl_deferred);
                                     ctr = (uu___355_18535.ctr);
                                     defer_ok = (uu___355_18535.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___355_18535.tcenv);
                                     wl_implicits =
                                       (uu___355_18535.wl_implicits)
                                   })
                                 in
                              solve env uu____18533  in
                            (match uu____18532 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____18539 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____18545,uu____18546) ->
                  let head1 =
                    let uu____18570 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18570
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18610 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18610
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18650 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18650
                    then
                      let uu____18651 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18652 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18653 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18651 uu____18652 uu____18653
                    else ());
                   (let uu____18655 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18655
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18662 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18662
                       then
                         let uu____18663 =
                           let uu____18670 =
                             let uu____18671 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18671 = FStar_Syntax_Util.Equal  in
                           if uu____18670
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18681 = mk_eq2 wl orig t1 t2  in
                              match uu____18681 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18663 with
                         | (guard,wl1) ->
                             let uu____18702 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18702
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18705,uu____18706) ->
                  let head1 =
                    let uu____18714 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18714
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18754 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18754
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18794 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18794
                    then
                      let uu____18795 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18796 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18797 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18795 uu____18796 uu____18797
                    else ());
                   (let uu____18799 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18799
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18806 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18806
                       then
                         let uu____18807 =
                           let uu____18814 =
                             let uu____18815 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18815 = FStar_Syntax_Util.Equal  in
                           if uu____18814
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18825 = mk_eq2 wl orig t1 t2  in
                              match uu____18825 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18807 with
                         | (guard,wl1) ->
                             let uu____18846 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18846
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18849,uu____18850) ->
                  let head1 =
                    let uu____18852 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18852
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18892 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18892
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18932 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18932
                    then
                      let uu____18933 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18934 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18935 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18933 uu____18934 uu____18935
                    else ());
                   (let uu____18937 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18937
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18944 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18944
                       then
                         let uu____18945 =
                           let uu____18952 =
                             let uu____18953 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18953 = FStar_Syntax_Util.Equal  in
                           if uu____18952
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18963 = mk_eq2 wl orig t1 t2  in
                              match uu____18963 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18945 with
                         | (guard,wl1) ->
                             let uu____18984 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18984
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18987,uu____18988) ->
                  let head1 =
                    let uu____18990 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18990
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19030 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19030
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19070 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19070
                    then
                      let uu____19071 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19072 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19073 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19071 uu____19072 uu____19073
                    else ());
                   (let uu____19075 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19075
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19082 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19082
                       then
                         let uu____19083 =
                           let uu____19090 =
                             let uu____19091 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19091 = FStar_Syntax_Util.Equal  in
                           if uu____19090
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19101 = mk_eq2 wl orig t1 t2  in
                              match uu____19101 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19083 with
                         | (guard,wl1) ->
                             let uu____19122 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19122
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____19125,uu____19126) ->
                  let head1 =
                    let uu____19128 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19128
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19168 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19168
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19208 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19208
                    then
                      let uu____19209 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19210 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19211 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19209 uu____19210 uu____19211
                    else ());
                   (let uu____19213 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19213
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19220 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19220
                       then
                         let uu____19221 =
                           let uu____19228 =
                             let uu____19229 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19229 = FStar_Syntax_Util.Equal  in
                           if uu____19228
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19239 = mk_eq2 wl orig t1 t2  in
                              match uu____19239 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19221 with
                         | (guard,wl1) ->
                             let uu____19260 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19260
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____19263,uu____19264) ->
                  let head1 =
                    let uu____19280 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19280
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19320 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19320
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19360 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19360
                    then
                      let uu____19361 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19362 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19363 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19361 uu____19362 uu____19363
                    else ());
                   (let uu____19365 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19365
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19372 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19372
                       then
                         let uu____19373 =
                           let uu____19380 =
                             let uu____19381 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19381 = FStar_Syntax_Util.Equal  in
                           if uu____19380
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19391 = mk_eq2 wl orig t1 t2  in
                              match uu____19391 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19373 with
                         | (guard,wl1) ->
                             let uu____19412 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19412
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19415,FStar_Syntax_Syntax.Tm_match uu____19416) ->
                  let head1 =
                    let uu____19440 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19440
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19480 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19480
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19520 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19520
                    then
                      let uu____19521 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19522 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19523 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19521 uu____19522 uu____19523
                    else ());
                   (let uu____19525 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19525
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19532 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19532
                       then
                         let uu____19533 =
                           let uu____19540 =
                             let uu____19541 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19541 = FStar_Syntax_Util.Equal  in
                           if uu____19540
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19551 = mk_eq2 wl orig t1 t2  in
                              match uu____19551 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19533 with
                         | (guard,wl1) ->
                             let uu____19572 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19572
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19575,FStar_Syntax_Syntax.Tm_uinst uu____19576) ->
                  let head1 =
                    let uu____19584 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19584
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19624 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19624
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19664 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19664
                    then
                      let uu____19665 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19666 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19667 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19665 uu____19666 uu____19667
                    else ());
                   (let uu____19669 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19669
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19676 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19676
                       then
                         let uu____19677 =
                           let uu____19684 =
                             let uu____19685 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19685 = FStar_Syntax_Util.Equal  in
                           if uu____19684
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19695 = mk_eq2 wl orig t1 t2  in
                              match uu____19695 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19677 with
                         | (guard,wl1) ->
                             let uu____19716 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19716
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19719,FStar_Syntax_Syntax.Tm_name uu____19720) ->
                  let head1 =
                    let uu____19722 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19722
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19762 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19762
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19802 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19802
                    then
                      let uu____19803 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19804 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19805 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19803 uu____19804 uu____19805
                    else ());
                   (let uu____19807 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19807
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19814 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19814
                       then
                         let uu____19815 =
                           let uu____19822 =
                             let uu____19823 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19823 = FStar_Syntax_Util.Equal  in
                           if uu____19822
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19833 = mk_eq2 wl orig t1 t2  in
                              match uu____19833 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19815 with
                         | (guard,wl1) ->
                             let uu____19854 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19854
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19857,FStar_Syntax_Syntax.Tm_constant uu____19858) ->
                  let head1 =
                    let uu____19860 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19860
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19894 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19894
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19928 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19928
                    then
                      let uu____19929 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19930 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19931 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19929 uu____19930 uu____19931
                    else ());
                   (let uu____19933 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19933
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19940 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19940
                       then
                         let uu____19941 =
                           let uu____19948 =
                             let uu____19949 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19949 = FStar_Syntax_Util.Equal  in
                           if uu____19948
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19959 = mk_eq2 wl orig t1 t2  in
                              match uu____19959 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19941 with
                         | (guard,wl1) ->
                             let uu____19980 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19980
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19983,FStar_Syntax_Syntax.Tm_fvar uu____19984) ->
                  let head1 =
                    let uu____19986 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19986
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20020 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20020
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20054 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20054
                    then
                      let uu____20055 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20056 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20057 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20055 uu____20056 uu____20057
                    else ());
                   (let uu____20059 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20059
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20066 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20066
                       then
                         let uu____20067 =
                           let uu____20074 =
                             let uu____20075 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20075 = FStar_Syntax_Util.Equal  in
                           if uu____20074
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20085 = mk_eq2 wl orig t1 t2  in
                              match uu____20085 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20067 with
                         | (guard,wl1) ->
                             let uu____20106 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20106
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____20109,FStar_Syntax_Syntax.Tm_app uu____20110) ->
                  let head1 =
                    let uu____20126 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20126
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20160 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20160
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20200 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20200
                    then
                      let uu____20201 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20202 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20203 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20201 uu____20202 uu____20203
                    else ());
                   (let uu____20205 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20205
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20212 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20212
                       then
                         let uu____20213 =
                           let uu____20220 =
                             let uu____20221 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20221 = FStar_Syntax_Util.Equal  in
                           if uu____20220
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20231 = mk_eq2 wl orig t1 t2  in
                              match uu____20231 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20213 with
                         | (guard,wl1) ->
                             let uu____20252 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20252
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____20255,FStar_Syntax_Syntax.Tm_let uu____20256) ->
                  let uu____20281 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____20281
                  then
                    let uu____20282 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____20282
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____20284,uu____20285) ->
                  let uu____20298 =
                    let uu____20303 =
                      let uu____20304 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20305 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20306 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20307 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20304 uu____20305 uu____20306 uu____20307
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20303)
                     in
                  FStar_Errors.raise_error uu____20298
                    t1.FStar_Syntax_Syntax.pos
              | (uu____20308,FStar_Syntax_Syntax.Tm_let uu____20309) ->
                  let uu____20322 =
                    let uu____20327 =
                      let uu____20328 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20329 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20330 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20331 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20328 uu____20329 uu____20330 uu____20331
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20327)
                     in
                  FStar_Errors.raise_error uu____20322
                    t1.FStar_Syntax_Syntax.pos
              | uu____20332 -> giveup env "head tag mismatch" orig))))

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
          (let uu____20391 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20391
           then
             let uu____20392 =
               let uu____20393 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____20393  in
             let uu____20394 =
               let uu____20395 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____20395  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____20392 uu____20394
           else ());
          (let uu____20397 =
             let uu____20398 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____20398  in
           if uu____20397
           then
             let uu____20399 =
               let uu____20400 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20401 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20400 uu____20401
                in
             giveup env uu____20399 orig
           else
             (let uu____20403 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____20403 with
              | (ret_sub_prob,wl1) ->
                  let uu____20410 =
                    FStar_List.fold_right2
                      (fun uu____20443  ->
                         fun uu____20444  ->
                           fun uu____20445  ->
                             match (uu____20443, uu____20444, uu____20445)
                             with
                             | ((a1,uu____20481),(a2,uu____20483),(arg_sub_probs,wl2))
                                 ->
                                 let uu____20504 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____20504 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____20410 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____20533 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____20533  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____20541 = attempt sub_probs wl3  in
                       solve env uu____20541)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20564 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20567)::[] -> wp1
              | uu____20584 ->
                  let uu____20593 =
                    let uu____20594 =
                      let uu____20595 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20595  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20594
                     in
                  failwith uu____20593
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20601 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20601]
              | x -> x  in
            let uu____20603 =
              let uu____20612 =
                let uu____20619 =
                  let uu____20620 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20620 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20619  in
              [uu____20612]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20603;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20633 = lift_c1 ()  in solve_eq uu____20633 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___303_20639  ->
                       match uu___303_20639 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20640 -> false))
                in
             let uu____20641 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20667)::uu____20668,(wp2,uu____20670)::uu____20671)
                   -> (wp1, wp2)
               | uu____20724 ->
                   let uu____20745 =
                     let uu____20750 =
                       let uu____20751 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20752 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20751 uu____20752
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20750)
                      in
                   FStar_Errors.raise_error uu____20745
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20641 with
             | (wpc1,wpc2) ->
                 let uu____20759 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20759
                 then
                   let uu____20762 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20762 wl
                 else
                   (let uu____20764 =
                      let uu____20771 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20771  in
                    match uu____20764 with
                    | (c2_decl,qualifiers) ->
                        let uu____20792 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20792
                        then
                          let c1_repr =
                            let uu____20796 =
                              let uu____20797 =
                                let uu____20798 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20798  in
                              let uu____20799 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20797 uu____20799
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20796
                             in
                          let c2_repr =
                            let uu____20801 =
                              let uu____20802 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20803 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20802 uu____20803
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20801
                             in
                          let uu____20804 =
                            let uu____20809 =
                              let uu____20810 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20811 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20810 uu____20811
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20809
                             in
                          (match uu____20804 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____20815 = attempt [prob] wl2  in
                               solve env uu____20815)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20826 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20826
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20829 =
                                     let uu____20836 =
                                       let uu____20837 =
                                         let uu____20852 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20855 =
                                           let uu____20864 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20871 =
                                             let uu____20880 =
                                               let uu____20887 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20887
                                                in
                                             [uu____20880]  in
                                           uu____20864 :: uu____20871  in
                                         (uu____20852, uu____20855)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20837
                                        in
                                     FStar_Syntax_Syntax.mk uu____20836  in
                                   uu____20829 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20928 =
                                    let uu____20935 =
                                      let uu____20936 =
                                        let uu____20951 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20954 =
                                          let uu____20963 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20970 =
                                            let uu____20979 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20986 =
                                              let uu____20995 =
                                                let uu____21002 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____21002
                                                 in
                                              [uu____20995]  in
                                            uu____20979 :: uu____20986  in
                                          uu____20963 :: uu____20970  in
                                        (uu____20951, uu____20954)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20936
                                       in
                                    FStar_Syntax_Syntax.mk uu____20935  in
                                  uu____20928 FStar_Pervasives_Native.None r)
                              in
                           let uu____21046 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____21046 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____21054 =
                                   let uu____21057 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____21057
                                    in
                                 solve_prob orig uu____21054 [] wl1  in
                               let uu____21060 = attempt [base_prob] wl2  in
                               solve env uu____21060)))
           in
        let uu____21061 = FStar_Util.physical_equality c1 c2  in
        if uu____21061
        then
          let uu____21062 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____21062
        else
          ((let uu____21065 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____21065
            then
              let uu____21066 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____21067 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____21066
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____21067
            else ());
           (let uu____21069 =
              let uu____21078 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____21081 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____21078, uu____21081)  in
            match uu____21069 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21099),FStar_Syntax_Syntax.Total
                    (t2,uu____21101)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21118 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21118 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21119,FStar_Syntax_Syntax.Total uu____21120) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21138),FStar_Syntax_Syntax.Total
                    (t2,uu____21140)) ->
                     let uu____21157 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21157 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21159),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21161)) ->
                     let uu____21178 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21178 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21180),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21182)) ->
                     let uu____21199 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21199 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21200,FStar_Syntax_Syntax.Comp uu____21201) ->
                     let uu____21210 =
                       let uu___356_21213 = problem  in
                       let uu____21216 =
                         let uu____21217 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21217
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___356_21213.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21216;
                         FStar_TypeChecker_Common.relation =
                           (uu___356_21213.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___356_21213.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___356_21213.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___356_21213.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___356_21213.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___356_21213.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___356_21213.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___356_21213.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21210 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21218,FStar_Syntax_Syntax.Comp uu____21219) ->
                     let uu____21228 =
                       let uu___356_21231 = problem  in
                       let uu____21234 =
                         let uu____21235 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21235
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___356_21231.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21234;
                         FStar_TypeChecker_Common.relation =
                           (uu___356_21231.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___356_21231.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___356_21231.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___356_21231.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___356_21231.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___356_21231.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___356_21231.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___356_21231.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21228 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21236,FStar_Syntax_Syntax.GTotal uu____21237) ->
                     let uu____21246 =
                       let uu___357_21249 = problem  in
                       let uu____21252 =
                         let uu____21253 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21253
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___357_21249.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___357_21249.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___357_21249.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21252;
                         FStar_TypeChecker_Common.element =
                           (uu___357_21249.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___357_21249.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___357_21249.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___357_21249.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___357_21249.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___357_21249.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21246 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21254,FStar_Syntax_Syntax.Total uu____21255) ->
                     let uu____21264 =
                       let uu___357_21267 = problem  in
                       let uu____21270 =
                         let uu____21271 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21271
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___357_21267.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___357_21267.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___357_21267.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21270;
                         FStar_TypeChecker_Common.element =
                           (uu___357_21267.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___357_21267.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___357_21267.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___357_21267.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___357_21267.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___357_21267.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21264 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21272,FStar_Syntax_Syntax.Comp uu____21273) ->
                     let uu____21274 =
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
                     if uu____21274
                     then
                       let uu____21275 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21275 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21279 =
                            let uu____21284 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____21284
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21290 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21291 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21290, uu____21291))
                             in
                          match uu____21279 with
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
                           (let uu____21298 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21298
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21300 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21300 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21303 =
                                  let uu____21304 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21305 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21304 uu____21305
                                   in
                                giveup env uu____21303 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21312 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21340  ->
              match uu____21340 with
              | (uu____21349,tm,uu____21351,uu____21352) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____21312 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21385 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21385 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21403 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21431  ->
                match uu____21431 with
                | (u1,u2) ->
                    let uu____21438 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21439 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21438 uu____21439))
         in
      FStar_All.pipe_right uu____21403 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21466,[])) -> "{}"
      | uu____21491 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21514 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21514
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21517 =
              FStar_List.map
                (fun uu____21527  ->
                   match uu____21527 with
                   | (uu____21532,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21517 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21537 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21537 imps
  
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
                  let uu____21590 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21590
                  then
                    let uu____21591 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21592 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21591
                      (rel_to_string rel) uu____21592
                  else "TOP"  in
                let uu____21594 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21594 with
                | (p,wl1) ->
                    (def_check_prob (Prims.strcat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
  
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
              let uu____21652 =
                let uu____21655 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21655
                 in
              FStar_Syntax_Syntax.new_bv uu____21652 t1  in
            let uu____21658 =
              let uu____21663 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21663
               in
            match uu____21658 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____21736 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21736
              then
                let uu____21737 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21737
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
          ((let uu____21759 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21759
            then
              let uu____21760 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21760
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21764 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21764
             then
               let uu____21765 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21765
             else ());
            (let f2 =
               let uu____21768 =
                 let uu____21769 = FStar_Syntax_Util.unmeta f1  in
                 uu____21769.FStar_Syntax_Syntax.n  in
               match uu____21768 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21773 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___358_21774 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___358_21774.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___358_21774.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___358_21774.FStar_TypeChecker_Env.implicits)
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
            let uu____21876 =
              let uu____21877 =
                let uu____21878 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21878;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21877  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21876
  
let with_guard_no_simp :
  'Auu____21893 .
    'Auu____21893 ->
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
            let uu____21916 =
              let uu____21917 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21917;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21916
  
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
          (let uu____21955 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21955
           then
             let uu____21956 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21957 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21956
               uu____21957
           else ());
          (let uu____21959 =
             let uu____21964 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____21964
              in
           match uu____21959 with
           | (prob,wl) ->
               let g =
                 let uu____21972 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21990  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21972  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22032 = try_teq true env t1 t2  in
        match uu____22032 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____22036 = FStar_TypeChecker_Env.get_range env  in
              let uu____22037 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____22036 uu____22037);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____22044 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____22044
              then
                let uu____22045 = FStar_Syntax_Print.term_to_string t1  in
                let uu____22046 = FStar_Syntax_Print.term_to_string t2  in
                let uu____22047 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____22045
                  uu____22046 uu____22047
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
          let uu____22069 = FStar_TypeChecker_Env.get_range env  in
          let uu____22070 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____22069 uu____22070
  
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
        (let uu____22095 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22095
         then
           let uu____22096 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____22097 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____22096 uu____22097
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____22100 =
           let uu____22107 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____22107 "sub_comp"
            in
         match uu____22100 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____22118 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____22136  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____22118)))
  
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
      fun uu____22189  ->
        match uu____22189 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22232 =
                 let uu____22237 =
                   let uu____22238 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22239 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22238 uu____22239
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22237)  in
               let uu____22240 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22232 uu____22240)
               in
            let equiv1 v1 v' =
              let uu____22252 =
                let uu____22257 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22258 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22257, uu____22258)  in
              match uu____22252 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22277 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22307 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22307 with
                      | FStar_Syntax_Syntax.U_unif uu____22314 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22343  ->
                                    match uu____22343 with
                                    | (u,v') ->
                                        let uu____22352 = equiv1 v1 v'  in
                                        if uu____22352
                                        then
                                          let uu____22355 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22355 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22371 -> []))
               in
            let uu____22376 =
              let wl =
                let uu___359_22380 = empty_worklist env  in
                {
                  attempting = (uu___359_22380.attempting);
                  wl_deferred = (uu___359_22380.wl_deferred);
                  ctr = (uu___359_22380.ctr);
                  defer_ok = false;
                  smt_ok = (uu___359_22380.smt_ok);
                  tcenv = (uu___359_22380.tcenv);
                  wl_implicits = (uu___359_22380.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22398  ->
                      match uu____22398 with
                      | (lb,v1) ->
                          let uu____22405 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22405 with
                           | USolved wl1 -> ()
                           | uu____22407 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22417 =
              match uu____22417 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22426) -> true
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
                      uu____22449,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22451,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22462) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22469,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22477 -> false)
               in
            let uu____22482 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22497  ->
                      match uu____22497 with
                      | (u,v1) ->
                          let uu____22504 = check_ineq (u, v1)  in
                          if uu____22504
                          then true
                          else
                            ((let uu____22507 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22507
                              then
                                let uu____22508 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22509 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22508
                                  uu____22509
                              else ());
                             false)))
               in
            if uu____22482
            then ()
            else
              ((let uu____22513 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22513
                then
                  ((let uu____22515 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22515);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22525 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22525))
                else ());
               (let uu____22535 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22535))
  
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
        let fail1 uu____22602 =
          match uu____22602 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___360_22623 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___360_22623.attempting);
            wl_deferred = (uu___360_22623.wl_deferred);
            ctr = (uu___360_22623.ctr);
            defer_ok;
            smt_ok = (uu___360_22623.smt_ok);
            tcenv = (uu___360_22623.tcenv);
            wl_implicits = (uu___360_22623.wl_implicits)
          }  in
        (let uu____22625 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22625
         then
           let uu____22626 = FStar_Util.string_of_bool defer_ok  in
           let uu____22627 = wl_to_string wl  in
           let uu____22628 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22626 uu____22627 uu____22628
         else ());
        (let g1 =
           let uu____22639 = solve_and_commit env wl fail1  in
           match uu____22639 with
           | FStar_Pervasives_Native.Some
               (uu____22646::uu____22647,uu____22648) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___361_22673 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___361_22673.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___361_22673.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22682 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___362_22690 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___362_22690.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___362_22690.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___362_22690.FStar_TypeChecker_Env.implicits)
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
    let uu____22738 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22738 with
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
            let uu___363_22861 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___363_22861.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___363_22861.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___363_22861.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22862 =
            let uu____22863 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22863  in
          if uu____22862
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22871 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22872 =
                       let uu____22873 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22873
                        in
                     FStar_Errors.diag uu____22871 uu____22872)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22877 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22878 =
                        let uu____22879 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22879
                         in
                      FStar_Errors.diag uu____22877 uu____22878)
                   else ();
                   (let uu____22882 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22882 "discharge_guard'"
                      env vc1);
                   (let uu____22883 = check_trivial vc1  in
                    match uu____22883 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22890 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22891 =
                                let uu____22892 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22892
                                 in
                              FStar_Errors.diag uu____22890 uu____22891)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22897 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22898 =
                                let uu____22899 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22899
                                 in
                              FStar_Errors.diag uu____22897 uu____22898)
                           else ();
                           (let vcs =
                              let uu____22912 = FStar_Options.use_tactics ()
                                 in
                              if uu____22912
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22934  ->
                                     (let uu____22936 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22936);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22979  ->
                                              match uu____22979 with
                                              | (env1,goal,opts) ->
                                                  let uu____22995 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22995, opts)))))
                              else
                                (let uu____22997 =
                                   let uu____23006 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____23006)  in
                                 [uu____22997])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____23049  ->
                                    match uu____23049 with
                                    | (env1,goal,opts) ->
                                        let uu____23065 = check_trivial goal
                                           in
                                        (match uu____23065 with
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
                                                (let uu____23073 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23074 =
                                                   let uu____23075 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____23076 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____23075 uu____23076
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23073 uu____23074)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____23079 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____23080 =
                                                   let uu____23081 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____23081
                                                    in
                                                 FStar_Errors.diag
                                                   uu____23079 uu____23080)
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
      let uu____23095 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23095 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____23102 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____23102
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____23113 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____23113 with
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
            let uu____23146 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____23146 with
            | FStar_Pervasives_Native.Some uu____23149 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____23169 = acc  in
            match uu____23169 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____23221 = hd1  in
                     (match uu____23221 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23235 = unresolved ctx_u  in
                             if uu____23235
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___364_23247 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___364_23247.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___364_23247.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___364_23247.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___364_23247.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___364_23247.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___364_23247.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___364_23247.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___364_23247.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___364_23247.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___364_23247.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___364_23247.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___364_23247.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___364_23247.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___364_23247.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___364_23247.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___364_23247.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___364_23247.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___364_23247.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___364_23247.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___364_23247.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___364_23247.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___364_23247.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___364_23247.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___364_23247.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___364_23247.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___364_23247.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___364_23247.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___364_23247.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___364_23247.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___364_23247.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___364_23247.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___364_23247.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___364_23247.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___364_23247.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___364_23247.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___364_23247.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___364_23247.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___364_23247.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___365_23250 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___365_23250.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___365_23250.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___365_23250.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___365_23250.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___365_23250.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___365_23250.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___365_23250.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___365_23250.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___365_23250.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___365_23250.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___365_23250.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___365_23250.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___365_23250.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___365_23250.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___365_23250.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___365_23250.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___365_23250.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___365_23250.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___365_23250.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___365_23250.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___365_23250.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___365_23250.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___365_23250.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___365_23250.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___365_23250.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___365_23250.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___365_23250.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___365_23250.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___365_23250.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___365_23250.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___365_23250.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___365_23250.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___365_23250.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___365_23250.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___365_23250.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___365_23250.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___365_23250.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___365_23250.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____23253 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23253
                                   then
                                     let uu____23254 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____23255 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____23256 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____23257 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____23254 uu____23255 uu____23256
                                       reason uu____23257
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____23268 =
                                             let uu____23277 =
                                               let uu____23284 =
                                                 let uu____23285 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____23286 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____23287 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____23285 uu____23286
                                                   uu____23287
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____23284, r)
                                                in
                                             [uu____23277]  in
                                           FStar_Errors.add_errors
                                             uu____23268);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___368_23301 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___368_23301.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___368_23301.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___368_23301.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____23304 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____23314  ->
                                               let uu____23315 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____23316 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____23317 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____23315 uu____23316
                                                 reason uu____23317)) env2 g2
                                         true
                                        in
                                     match uu____23304 with
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
          let uu___369_23327 = g  in
          let uu____23328 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___369_23327.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___369_23327.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___369_23327.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23328
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
        let uu____23378 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23378 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23387 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23387
      | (reason,e,ctx_u,r)::uu____23392 ->
          let uu____23411 =
            let uu____23416 =
              let uu____23417 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23418 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23417 uu____23418 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23416)
             in
          FStar_Errors.raise_error uu____23411 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___370_23429 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___370_23429.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___370_23429.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___370_23429.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23444 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23444 with
      | FStar_Pervasives_Native.Some uu____23450 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23466 = try_teq false env t1 t2  in
        match uu____23466 with
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
        (let uu____23500 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23500
         then
           let uu____23501 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23502 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23501
             uu____23502
         else ());
        (let uu____23504 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23504 with
         | (prob,x,wl) ->
             let g =
               let uu____23523 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23541  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23523  in
             ((let uu____23569 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23569
               then
                 let uu____23570 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23571 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23572 =
                   let uu____23573 = FStar_Util.must g  in
                   guard_to_string env uu____23573  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23570 uu____23571 uu____23572
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
        let uu____23607 = check_subtyping env t1 t2  in
        match uu____23607 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23626 =
              let uu____23627 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23627 g  in
            FStar_Pervasives_Native.Some uu____23626
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23645 = check_subtyping env t1 t2  in
        match uu____23645 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23664 =
              let uu____23665 =
                let uu____23666 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23666]  in
              close_guard env uu____23665 g  in
            FStar_Pervasives_Native.Some uu____23664
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23695 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23695
         then
           let uu____23696 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23697 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23696
             uu____23697
         else ());
        (let uu____23699 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23699 with
         | (prob,x,wl) ->
             let g =
               let uu____23712 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23730  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23712  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23759 =
                      let uu____23760 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23760]  in
                    close_guard env uu____23759 g1  in
                  discharge_guard_nosmt env g2))
  