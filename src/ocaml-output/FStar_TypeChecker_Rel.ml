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
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
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
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___284_1599  ->
    match uu___284_1599 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1618 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1618) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1646 =
          let uu____1647 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1647  in
        if uu____1646
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1681)::bs ->
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
        let uu____1748 =
          let uu____1749 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1749  in
        if uu____1748
        then ()
        else
          (let uu____1751 =
             let uu____1754 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1754
              in
           def_check_closed_in (p_loc prob) msg uu____1751 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1792 =
          let uu____1793 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1793  in
        if uu____1792
        then ()
        else
          (let uu____1795 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1795)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1810 =
        let uu____1811 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1811  in
      if uu____1810
      then ()
      else
        (let msgf m =
           let uu____1819 =
             let uu____1820 =
               let uu____1821 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1821 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1820  in
           Prims.strcat msg uu____1819  in
         (let uu____1823 = msgf "scope"  in
          let uu____1824 = p_scope prob  in
          def_scope_wf uu____1823 (p_loc prob) uu____1824);
         (let uu____1832 = msgf "guard"  in
          def_check_scoped uu____1832 prob (p_guard prob));
         (match p_element prob with
          | FStar_Pervasives_Native.Some t ->
              def_check_scoped (Prims.strcat "element." msg) prob t
          | FStar_Pervasives_Native.None  -> ());
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1839 = msgf "lhs"  in
                def_check_scoped uu____1839 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1840 = msgf "rhs"  in
                def_check_scoped uu____1840 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1845 = msgf "lhs"  in
                def_check_scoped_comp uu____1845 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1846 = msgf "rhs"  in
                def_check_scoped_comp uu____1846 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___314_1862 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___314_1862.wl_deferred);
          ctr = (uu___314_1862.ctr);
          defer_ok = (uu___314_1862.defer_ok);
          smt_ok;
          tcenv = (uu___314_1862.tcenv);
          wl_implicits = (uu___314_1862.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1869 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1869,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___315_1892 = empty_worklist env  in
      let uu____1893 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1893;
        wl_deferred = (uu___315_1892.wl_deferred);
        ctr = (uu___315_1892.ctr);
        defer_ok = (uu___315_1892.defer_ok);
        smt_ok = (uu___315_1892.smt_ok);
        tcenv = (uu___315_1892.tcenv);
        wl_implicits = (uu___315_1892.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___316_1913 = wl  in
        {
          attempting = (uu___316_1913.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___316_1913.ctr);
          defer_ok = (uu___316_1913.defer_ok);
          smt_ok = (uu___316_1913.smt_ok);
          tcenv = (uu___316_1913.tcenv);
          wl_implicits = (uu___316_1913.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___317_1935 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___317_1935.wl_deferred);
         ctr = (uu___317_1935.ctr);
         defer_ok = (uu___317_1935.defer_ok);
         smt_ok = (uu___317_1935.smt_ok);
         tcenv = (uu___317_1935.tcenv);
         wl_implicits = (uu___317_1935.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1946 .
    worklist ->
      'Auu____1946 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1975 = FStar_Syntax_Util.type_u ()  in
          match uu____1975 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1987 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1987 with
               | (uu____1998,tt,wl1) ->
                   let uu____2001 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____2001, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___285_2006  ->
    match uu___285_2006 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2022 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2022 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____2032  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2130 .
    worklist ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2130 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2130 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2130 FStar_TypeChecker_Common.problem,worklist)
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
                  let env = FStar_TypeChecker_Env.push_binders wl.tcenv scope
                     in
                  let uu____2182 =
                    let uu____2189 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      env.FStar_TypeChecker_Env.gamma uu____2189
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2182 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2208 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2208;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ([], ctx_uvar);
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (mk_t_problem :
  worklist ->
    FStar_Syntax_Syntax.binders ->
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
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu____2264 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2264 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    FStar_Syntax_Syntax.binders ->
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
                  def_check_prob (Prims.strcat reason ".mk_c.arg") orig;
                  (let uu____2331 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2331 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2367 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2367 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2367 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2367 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2418 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2455 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2455]  in
                        let uu____2468 =
                          let uu____2471 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2471  in
                        let uu____2474 =
                          let uu____2477 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2477  in
                        (bs, uu____2468, uu____2474)
                     in
                  match uu____2418 with
                  | (bs,lg_ty,elt) ->
                      let uu____2499 =
                        let uu____2506 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___318_2514 = wl  in
                           {
                             attempting = (uu___318_2514.attempting);
                             wl_deferred = (uu___318_2514.wl_deferred);
                             ctr = (uu___318_2514.ctr);
                             defer_ok = (uu___318_2514.defer_ok);
                             smt_ok = (uu___318_2514.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___318_2514.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2506
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2499 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2526 =
                                   let uu____2531 =
                                     let uu____2532 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2532]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2531
                                    in
                                 uu____2526 FStar_Pervasives_Native.None loc
                              in
                           let prob =
                             let uu____2556 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2556;
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
                           (prob, wl1))
  
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
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
                let uu____2598 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2598;
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
  'Auu____2610 .
    worklist ->
      'Auu____2610 FStar_TypeChecker_Common.problem ->
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
        let uu____2660 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2660
        then
          let uu____2661 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2662 = prob_to_string env d  in
          let uu____2663 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2661 uu____2662 uu____2663 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2669 -> failwith "impossible"  in
           let uu____2670 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2682 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2683 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2682, uu____2683)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2687 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2688 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2687, uu____2688)
              in
           match uu____2670 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___286_2706  ->
            match uu___286_2706 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2718 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2722 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  def_check_closed_in t.FStar_Syntax_Syntax.pos "commit"
                    uu____2722 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___287_2747  ->
           match uu___287_2747 with
           | UNIV uu____2750 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2757 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2757
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
        (fun uu___288_2781  ->
           match uu___288_2781 with
           | UNIV (u',t) ->
               let uu____2786 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2786
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2790 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2801 =
        let uu____2802 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2802
         in
      FStar_Syntax_Subst.compress uu____2801
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2813 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2813
  
let norm_arg :
  'Auu____2820 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2820) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2820)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2843 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2843, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2884  ->
              match uu____2884 with
              | (x,imp) ->
                  let uu____2895 =
                    let uu___319_2896 = x  in
                    let uu____2897 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___319_2896.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___319_2896.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2897
                    }  in
                  (uu____2895, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2918 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2918
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2922 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2922
        | uu____2925 -> u2  in
      let uu____2926 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2926
  
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
                (let uu____3048 = norm_refinement env t12  in
                 match uu____3048 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3065;
                     FStar_Syntax_Syntax.vars = uu____3066;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3092 =
                       let uu____3093 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3094 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3093 uu____3094
                        in
                     failwith uu____3092)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3110 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3110
          | FStar_Syntax_Syntax.Tm_uinst uu____3111 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3150 =
                   let uu____3151 = FStar_Syntax_Subst.compress t1'  in
                   uu____3151.FStar_Syntax_Syntax.n  in
                 match uu____3150 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3168 -> aux true t1'
                 | uu____3175 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3192 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3225 =
                   let uu____3226 = FStar_Syntax_Subst.compress t1'  in
                   uu____3226.FStar_Syntax_Syntax.n  in
                 match uu____3225 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3243 -> aux true t1'
                 | uu____3250 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3267 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3314 =
                   let uu____3315 = FStar_Syntax_Subst.compress t1'  in
                   uu____3315.FStar_Syntax_Syntax.n  in
                 match uu____3314 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3332 -> aux true t1'
                 | uu____3339 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3356 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3373 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3390 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3407 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3424 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3453 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3486 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3509 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3540 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3569 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3608 ->
              let uu____3615 =
                let uu____3616 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3617 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3616 uu____3617
                 in
              failwith uu____3615
          | FStar_Syntax_Syntax.Tm_ascribed uu____3632 ->
              let uu____3659 =
                let uu____3660 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3661 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3660 uu____3661
                 in
              failwith uu____3659
          | FStar_Syntax_Syntax.Tm_delayed uu____3676 ->
              let uu____3701 =
                let uu____3702 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3703 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3702 uu____3703
                 in
              failwith uu____3701
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3718 =
                let uu____3719 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3720 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3719 uu____3720
                 in
              failwith uu____3718
           in
        let uu____3735 = whnf env t1  in aux false uu____3735
  
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
      let uu____3781 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3781 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3817 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3817, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3828 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3828 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                      FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3855 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3855 with
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
  fun uu____3942  ->
    match uu____3942 with
    | (t_base,refopt) ->
        let uu____3975 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3975 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4015 =
      let uu____4018 =
        let uu____4021 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4044  ->
                  match uu____4044 with | (uu____4051,uu____4052,x) -> x))
           in
        FStar_List.append wl.attempting uu____4021  in
      FStar_List.map (wl_prob_to_string wl) uu____4018  in
    FStar_All.pipe_right uu____4015 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4066 .
    ('Auu____4066,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4077  ->
    match uu____4077 with
    | (uu____4084,c,args) ->
        let uu____4087 = print_ctx_uvar c  in
        let uu____4088 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4087 uu____4088
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4094 = FStar_Syntax_Util.head_and_args t  in
    match uu____4094 with
    | (head1,_args) ->
        let uu____4131 =
          let uu____4132 = FStar_Syntax_Subst.compress head1  in
          uu____4132.FStar_Syntax_Syntax.n  in
        (match uu____4131 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4135 -> true
         | uu____4150 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4156 = FStar_Syntax_Util.head_and_args t  in
    match uu____4156 with
    | (head1,_args) ->
        let uu____4193 =
          let uu____4194 = FStar_Syntax_Subst.compress head1  in
          uu____4194.FStar_Syntax_Syntax.n  in
        (match uu____4193 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4198) -> u
         | uu____4219 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4242 = FStar_Syntax_Util.head_and_args t  in
      match uu____4242 with
      | (head1,args) ->
          let uu____4283 =
            let uu____4284 = FStar_Syntax_Subst.compress head1  in
            uu____4284.FStar_Syntax_Syntax.n  in
          (match uu____4283 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4292)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4335 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___289_4360  ->
                         match uu___289_4360 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4364 =
                               let uu____4365 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4365.FStar_Syntax_Syntax.n  in
                             (match uu____4364 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4369 -> false)
                         | uu____4370 -> true))
                  in
               (match uu____4335 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4392 =
                        FStar_List.collect
                          (fun uu___290_4402  ->
                             match uu___290_4402 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4406 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4406]
                             | uu____4407 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4392 FStar_List.rev  in
                    let uu____4424 =
                      let uu____4431 =
                        let uu____4438 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___291_4456  ->
                                  match uu___291_4456 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4460 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4460]
                                  | uu____4461 -> []))
                           in
                        FStar_All.pipe_right uu____4438 FStar_List.rev  in
                      let uu____4478 =
                        let uu____4481 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4481  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4431 uu____4478
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4424 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4510  ->
                                match uu____4510 with
                                | (x,i) ->
                                    let uu____4521 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4521, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4544  ->
                                match uu____4544 with
                                | (a,i) ->
                                    let uu____4555 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4555, i)) args_sol
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
           | uu____4571 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4591 =
          let uu____4612 =
            let uu____4613 = FStar_Syntax_Subst.compress k  in
            uu____4613.FStar_Syntax_Syntax.n  in
          match uu____4612 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4682 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4682)
              else
                (let uu____4712 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4712 with
                 | (ys',t1,uu____4743) ->
                     let uu____4748 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4748))
          | uu____4781 ->
              let uu____4782 =
                let uu____4787 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4787)  in
              ((ys, t), uu____4782)
           in
        match uu____4591 with
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
                 let uu____4864 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4864 c  in
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
               (let uu____4938 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4938
                then
                  let uu____4939 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4940 = print_ctx_uvar uv  in
                  let uu____4941 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4939 uu____4940 uu____4941
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4947 =
                   let uu____4948 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4948  in
                 let uu____4949 =
                   let uu____4952 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4952
                    in
                 def_check_closed_in (p_loc prob) uu____4947 uu____4949 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uu____4971 = p_guard_uvar prob  in
             match uu____4971 with
             | (xs,uv) ->
                 let fail1 uu____4983 =
                   let uu____4984 =
                     let uu____4985 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4986 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4985 uu____4986
                      in
                   failwith uu____4984  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____5036  ->
                           match uu____5036 with
                           | (a,i) ->
                               let uu____5049 =
                                 let uu____5050 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____5050.FStar_Syntax_Syntax.n  in
                               (match uu____5049 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____5068 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____5076 =
                     let uu____5077 = is_flex g  in
                     Prims.op_Negation uu____5077  in
                   if uu____5076
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____5081 = destruct_flex_t g wl  in
                      match uu____5081 with
                      | ((uu____5086,uv1,args),wl1) ->
                          ((let uu____5091 = args_as_binders args  in
                            assign_solution uu____5091 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___320_5093 = wl1  in
                   {
                     attempting = (uu___320_5093.attempting);
                     wl_deferred = (uu___320_5093.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___320_5093.defer_ok);
                     smt_ok = (uu___320_5093.smt_ok);
                     tcenv = (uu___320_5093.tcenv);
                     wl_implicits = (uu___320_5093.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5114 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5114
         then
           let uu____5115 = FStar_Util.string_of_int pid  in
           let uu____5116 =
             let uu____5117 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5117 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5115 uu____5116
         else ());
        commit sol;
        (let uu___321_5124 = wl  in
         {
           attempting = (uu___321_5124.attempting);
           wl_deferred = (uu___321_5124.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___321_5124.defer_ok);
           smt_ok = (uu___321_5124.smt_ok);
           tcenv = (uu___321_5124.tcenv);
           wl_implicits = (uu___321_5124.wl_implicits)
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
             | (uu____5186,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5214 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5214
              in
           (let uu____5220 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5220
            then
              let uu____5221 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5222 =
                let uu____5223 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5223 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5221 uu____5222
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
        let uu____5248 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5248 FStar_Util.set_elements  in
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
      let uu____5282 = occurs uk t  in
      match uu____5282 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5311 =
                 let uu____5312 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5313 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5312 uu____5313
                  in
               FStar_Pervasives_Native.Some uu____5311)
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
            let uu____5402 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5402 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5446 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5494  ->
             match uu____5494 with
             | (x,uu____5504) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5517 = FStar_List.last bs  in
      match uu____5517 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5535) ->
          let uu____5540 =
            FStar_Util.prefix_until
              (fun uu___292_5555  ->
                 match uu___292_5555 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5557 -> false) g
             in
          (match uu____5540 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5570,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5606 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5606 with
        | (pfx,uu____5616) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5628 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5628 with
             | (uu____5635,src',wl1) ->
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
                 | uu____5735 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5736 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5790  ->
                  fun uu____5791  ->
                    match (uu____5790, uu____5791) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5872 =
                          let uu____5873 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5873
                           in
                        if uu____5872
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5898 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5898
                           then
                             let uu____5911 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5911)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5736 with | (isect,uu____5948) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5977 'Auu____5978 .
    (FStar_Syntax_Syntax.bv,'Auu____5977) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5978) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6035  ->
              fun uu____6036  ->
                match (uu____6035, uu____6036) with
                | ((a,uu____6054),(b,uu____6056)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6071 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6071) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6101  ->
           match uu____6101 with
           | (y,uu____6107) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6116 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6116) FStar_Pervasives_Native.tuple2
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
                   let uu____6246 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6246
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6266 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6309 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6347 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6360 -> false
  
let string_of_option :
  'Auu____6367 .
    ('Auu____6367 -> Prims.string) ->
      'Auu____6367 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___293_6382  ->
      match uu___293_6382 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6388 = f x  in Prims.strcat "Some " uu____6388
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___294_6393  ->
    match uu___294_6393 with
    | MisMatch (d1,d2) ->
        let uu____6404 =
          let uu____6405 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6406 =
            let uu____6407 =
              let uu____6408 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6408 ")"  in
            Prims.strcat ") (" uu____6407  in
          Prims.strcat uu____6405 uu____6406  in
        Prims.strcat "MisMatch (" uu____6404
    | HeadMatch u ->
        let uu____6410 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6410
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___295_6415  ->
    match uu___295_6415 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6430 -> HeadMatch false
  
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
          let uu____6444 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6444 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6455 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6478 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6487 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6515 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6515
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6516 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6517 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6518 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6533 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6546 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6570) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6576,uu____6577) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6619) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6640;
             FStar_Syntax_Syntax.index = uu____6641;
             FStar_Syntax_Syntax.sort = t2;_},uu____6643)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6650 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6651 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6652 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6665 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6672 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6690 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6690
  
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
            let uu____6717 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6717
            then FullMatch
            else
              (let uu____6719 =
                 let uu____6728 =
                   let uu____6731 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6731  in
                 let uu____6732 =
                   let uu____6735 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6735  in
                 (uu____6728, uu____6732)  in
               MisMatch uu____6719)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6741),FStar_Syntax_Syntax.Tm_uinst (g,uu____6743)) ->
            let uu____6752 = head_matches env f g  in
            FStar_All.pipe_right uu____6752 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6755 = FStar_Const.eq_const c d  in
            if uu____6755
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6762),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6764)) ->
            let uu____6805 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6805
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6812),FStar_Syntax_Syntax.Tm_refine (y,uu____6814)) ->
            let uu____6823 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6823 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6825),uu____6826) ->
            let uu____6831 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6831 head_match
        | (uu____6832,FStar_Syntax_Syntax.Tm_refine (x,uu____6834)) ->
            let uu____6839 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6839 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6840,FStar_Syntax_Syntax.Tm_type
           uu____6841) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6842,FStar_Syntax_Syntax.Tm_arrow uu____6843) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6869),FStar_Syntax_Syntax.Tm_app (head',uu____6871))
            ->
            let uu____6912 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6912 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6914),uu____6915) ->
            let uu____6936 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6936 head_match
        | (uu____6937,FStar_Syntax_Syntax.Tm_app (head1,uu____6939)) ->
            let uu____6960 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6960 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6961,FStar_Syntax_Syntax.Tm_let
           uu____6962) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6987,FStar_Syntax_Syntax.Tm_match uu____6988) ->
            HeadMatch true
        | uu____7033 ->
            let uu____7038 =
              let uu____7047 = delta_depth_of_term env t11  in
              let uu____7050 = delta_depth_of_term env t21  in
              (uu____7047, uu____7050)  in
            MisMatch uu____7038
  
let head_matches_delta :
  'Auu____7067 .
    FStar_TypeChecker_Env.env ->
      'Auu____7067 ->
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
            (let uu____7116 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7116
             then
               let uu____7117 = FStar_Syntax_Print.term_to_string t  in
               let uu____7118 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7117 uu____7118
             else ());
            (let uu____7120 =
               let uu____7121 = FStar_Syntax_Util.un_uinst head1  in
               uu____7121.FStar_Syntax_Syntax.n  in
             match uu____7120 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7127 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7127 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7141 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7141
                        then
                          let uu____7142 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7142
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7144 ->
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
                      ((let uu____7155 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7155
                        then
                          let uu____7156 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7157 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7156
                            uu____7157
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7159 -> FStar_Pervasives_Native.None)
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
            (let uu____7297 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7297
             then
               let uu____7298 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7299 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7300 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7298
                 uu____7299 uu____7300
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7324 =
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
               match uu____7324 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7369 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7369 with
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
                  uu____7401),uu____7402)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7420 =
                      let uu____7429 = maybe_inline t11  in
                      let uu____7432 = maybe_inline t21  in
                      (uu____7429, uu____7432)  in
                    match uu____7420 with
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
                 (uu____7469,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7470))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7488 =
                      let uu____7497 = maybe_inline t11  in
                      let uu____7500 = maybe_inline t21  in
                      (uu____7497, uu____7500)  in
                    match uu____7488 with
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
             | MisMatch uu____7549 -> fail1 n_delta r t11 t21
             | uu____7558 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7571 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7571
           then
             let uu____7572 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7573 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7574 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7581 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7599 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7599
                    (fun uu____7633  ->
                       match uu____7633 with
                       | (t11,t21) ->
                           let uu____7640 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7641 =
                             let uu____7642 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7642  in
                           Prims.strcat uu____7640 uu____7641))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7572 uu____7573 uu____7574 uu____7581
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7654 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7654 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___296_7667  ->
    match uu___296_7667 with
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
      let uu___322_7704 = p  in
      let uu____7707 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7708 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___322_7704.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7707;
        FStar_TypeChecker_Common.relation =
          (uu___322_7704.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7708;
        FStar_TypeChecker_Common.element =
          (uu___322_7704.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___322_7704.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___322_7704.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___322_7704.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___322_7704.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___322_7704.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7722 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7722
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7727 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7749 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7749 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7757 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7757 with
           | (lh,lhs_args) ->
               let uu____7798 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7798 with
                | (rh,rhs_args) ->
                    let uu____7839 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7852,FStar_Syntax_Syntax.Tm_uvar uu____7853)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7934 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7957,uu____7958)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7975,FStar_Syntax_Syntax.Tm_uvar uu____7976)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7993,FStar_Syntax_Syntax.Tm_arrow uu____7994)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___323_8024 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___323_8024.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___323_8024.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___323_8024.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___323_8024.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___323_8024.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___323_8024.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___323_8024.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___323_8024.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___323_8024.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8027,FStar_Syntax_Syntax.Tm_type uu____8028)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___323_8046 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___323_8046.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___323_8046.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___323_8046.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___323_8046.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___323_8046.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___323_8046.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___323_8046.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___323_8046.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___323_8046.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8049,FStar_Syntax_Syntax.Tm_uvar uu____8050)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___323_8068 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___323_8068.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___323_8068.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___323_8068.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___323_8068.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___323_8068.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___323_8068.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___323_8068.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___323_8068.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___323_8068.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8071,FStar_Syntax_Syntax.Tm_uvar uu____8072)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8089,uu____8090)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8107,FStar_Syntax_Syntax.Tm_uvar uu____8108)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8125,uu____8126) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7839 with
                     | (rank,tp1) ->
                         let uu____8139 =
                           FStar_All.pipe_right
                             (let uu___324_8143 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___324_8143.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___324_8143.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___324_8143.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___324_8143.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___324_8143.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___324_8143.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___324_8143.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___324_8143.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___324_8143.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8139))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8149 =
            FStar_All.pipe_right
              (let uu___325_8153 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___325_8153.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___325_8153.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___325_8153.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___325_8153.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___325_8153.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___325_8153.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___325_8153.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___325_8153.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___325_8153.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8149)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8214 probs =
      match uu____8214 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8295 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8316 = rank wl.tcenv hd1  in
               (match uu____8316 with
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
                      (let uu____8375 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8379 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8379)
                          in
                       if uu____8375
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
          let uu____8447 = FStar_Syntax_Util.head_and_args t  in
          match uu____8447 with
          | (hd1,uu____8463) ->
              let uu____8484 =
                let uu____8485 = FStar_Syntax_Subst.compress hd1  in
                uu____8485.FStar_Syntax_Syntax.n  in
              (match uu____8484 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8489) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8523  ->
                           match uu____8523 with
                           | (y,uu____8529) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8543  ->
                                       match uu____8543 with
                                       | (x,uu____8549) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8550 -> false)
           in
        let uu____8551 = rank tcenv p  in
        match uu____8551 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8558 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8585 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8599 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8613 -> false
  
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
                        let uu____8665 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8665 with
                        | (k,uu____8671) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8681 -> false)))
            | uu____8682 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8734 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8740 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8740 = (Prims.parse_int "0")))
                           in
                        if uu____8734 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8756 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8762 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8762 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8756)
               in
            let uu____8763 = filter1 u12  in
            let uu____8766 = filter1 u22  in (uu____8763, uu____8766)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8795 = filter_out_common_univs us1 us2  in
                (match uu____8795 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8854 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8854 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8857 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8867 =
                          let uu____8868 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8869 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8868
                            uu____8869
                           in
                        UFailed uu____8867))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8893 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8893 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8919 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8919 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8922 ->
                let uu____8927 =
                  let uu____8928 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8929 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8928
                    uu____8929 msg
                   in
                UFailed uu____8927
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8930,uu____8931) ->
              let uu____8932 =
                let uu____8933 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8934 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8933 uu____8934
                 in
              failwith uu____8932
          | (FStar_Syntax_Syntax.U_unknown ,uu____8935) ->
              let uu____8936 =
                let uu____8937 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8938 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8937 uu____8938
                 in
              failwith uu____8936
          | (uu____8939,FStar_Syntax_Syntax.U_bvar uu____8940) ->
              let uu____8941 =
                let uu____8942 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8943 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8942 uu____8943
                 in
              failwith uu____8941
          | (uu____8944,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8945 =
                let uu____8946 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8947 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8946 uu____8947
                 in
              failwith uu____8945
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8971 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8971
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8985 = occurs_univ v1 u3  in
              if uu____8985
              then
                let uu____8986 =
                  let uu____8987 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8988 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8987 uu____8988
                   in
                try_umax_components u11 u21 uu____8986
              else
                (let uu____8990 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8990)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____9002 = occurs_univ v1 u3  in
              if uu____9002
              then
                let uu____9003 =
                  let uu____9004 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____9005 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9004 uu____9005
                   in
                try_umax_components u11 u21 uu____9003
              else
                (let uu____9007 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____9007)
          | (FStar_Syntax_Syntax.U_max uu____9008,uu____9009) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9015 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9015
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9017,FStar_Syntax_Syntax.U_max uu____9018) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9024 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9024
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9026,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9027,FStar_Syntax_Syntax.U_name
             uu____9028) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9029) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9030) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9031,FStar_Syntax_Syntax.U_succ
             uu____9032) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9033,FStar_Syntax_Syntax.U_zero
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
      let uu____9133 = bc1  in
      match uu____9133 with
      | (bs1,mk_cod1) ->
          let uu____9177 = bc2  in
          (match uu____9177 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9288 = aux xs ys  in
                     (match uu____9288 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9371 =
                       let uu____9378 = mk_cod1 xs  in ([], uu____9378)  in
                     let uu____9381 =
                       let uu____9388 = mk_cod2 ys  in ([], uu____9388)  in
                     (uu____9371, uu____9381)
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
                  let uu____9458 =
                    let uu____9459 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9459 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9458
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9464 = has_type_guard t1 t2  in (uu____9464, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9465 = has_type_guard t2 t1  in (uu____9465, wl)
  
let is_flex_pat :
  'Auu____9474 'Auu____9475 'Auu____9476 .
    ('Auu____9474,'Auu____9475,'Auu____9476 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___297_9489  ->
    match uu___297_9489 with
    | (uu____9498,uu____9499,[]) -> true
    | uu____9502 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9533 = f  in
      match uu____9533 with
      | (uu____9540,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9541;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9542;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9545;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9546;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9547;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9599  ->
                 match uu____9599 with
                 | (y,uu____9605) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9727 =
                  let uu____9740 =
                    let uu____9743 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9743  in
                  ((FStar_List.rev pat_binders), uu____9740)  in
                FStar_Pervasives_Native.Some uu____9727
            | (uu____9770,[]) ->
                let uu____9793 =
                  let uu____9806 =
                    let uu____9809 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9809  in
                  ((FStar_List.rev pat_binders), uu____9806)  in
                FStar_Pervasives_Native.Some uu____9793
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9874 =
                  let uu____9875 = FStar_Syntax_Subst.compress a  in
                  uu____9875.FStar_Syntax_Syntax.n  in
                (match uu____9874 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9893 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9893
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___326_9914 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___326_9914.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___326_9914.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9918 =
                            let uu____9919 =
                              let uu____9926 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9926)  in
                            FStar_Syntax_Syntax.NT uu____9919  in
                          [uu____9918]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___327_9938 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___327_9938.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___327_9938.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9939 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9967 =
                  let uu____9980 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9980  in
                (match uu____9967 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10043 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10070 ->
               let uu____10071 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10071 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10347 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10347
       then
         let uu____10348 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10348
       else ());
      (let uu____10350 = next_prob probs  in
       match uu____10350 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___328_10377 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___328_10377.wl_deferred);
               ctr = (uu___328_10377.ctr);
               defer_ok = (uu___328_10377.defer_ok);
               smt_ok = (uu___328_10377.smt_ok);
               tcenv = (uu___328_10377.tcenv);
               wl_implicits = (uu___328_10377.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10385 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10385
                 then
                   let uu____10386 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10386
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
                           (let uu___329_10391 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___329_10391.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___329_10391.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___329_10391.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___329_10391.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___329_10391.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___329_10391.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___329_10391.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___329_10391.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___329_10391.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10413 ->
                let uu____10422 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10481  ->
                          match uu____10481 with
                          | (c,uu____10489,uu____10490) -> c < probs.ctr))
                   in
                (match uu____10422 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10531 =
                            let uu____10536 =
                              FStar_List.map
                                (fun uu____10551  ->
                                   match uu____10551 with
                                   | (uu____10562,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10536, (probs.wl_implicits))  in
                          Success uu____10531
                      | uu____10565 ->
                          let uu____10574 =
                            let uu___330_10575 = probs  in
                            let uu____10576 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10595  ->
                                      match uu____10595 with
                                      | (uu____10602,uu____10603,y) -> y))
                               in
                            {
                              attempting = uu____10576;
                              wl_deferred = rest;
                              ctr = (uu___330_10575.ctr);
                              defer_ok = (uu___330_10575.defer_ok);
                              smt_ok = (uu___330_10575.smt_ok);
                              tcenv = (uu___330_10575.tcenv);
                              wl_implicits = (uu___330_10575.wl_implicits)
                            }  in
                          solve env uu____10574))))

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
            let uu____10610 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10610 with
            | USolved wl1 ->
                let uu____10612 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10612
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
                  let uu____10664 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10664 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10667 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10679;
                  FStar_Syntax_Syntax.vars = uu____10680;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10683;
                  FStar_Syntax_Syntax.vars = uu____10684;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10696,uu____10697) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10704,FStar_Syntax_Syntax.Tm_uinst uu____10705) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10712 -> USolved wl

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
            ((let uu____10722 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10722
              then
                let uu____10723 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10723 msg
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
               let uu____10809 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10809 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10862 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10862
                then
                  let uu____10863 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10864 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10863 uu____10864
                else ());
               (let uu____10866 = head_matches_delta env1 () t1 t2  in
                match uu____10866 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10911 = eq_prob t1 t2 wl2  in
                         (match uu____10911 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____10932 ->
                         let uu____10941 = eq_prob t1 t2 wl2  in
                         (match uu____10941 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____10990 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11005 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11006 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11005, uu____11006)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11011 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11012 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11011, uu____11012)
                            in
                         (match uu____10990 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11043 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11043 with
                                | (t1_hd,t1_args) ->
                                    let uu____11082 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11082 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11136 =
                                              let uu____11143 =
                                                let uu____11152 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11152 :: t1_args  in
                                              let uu____11165 =
                                                let uu____11172 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11172 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11213  ->
                                                   fun uu____11214  ->
                                                     fun uu____11215  ->
                                                       match (uu____11213,
                                                               uu____11214,
                                                               uu____11215)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11257),
                                                          (a2,uu____11259))
                                                           ->
                                                           let uu____11284 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11284
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11143
                                                uu____11165
                                               in
                                            match uu____11136 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___331_11310 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___331_11310.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___331_11310.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11326 =
                                                  solve env1 wl'  in
                                                (match uu____11326 with
                                                 | Success (uu____11329,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___332_11333
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___332_11333.attempting);
                                                            wl_deferred =
                                                              (uu___332_11333.wl_deferred);
                                                            ctr =
                                                              (uu___332_11333.ctr);
                                                            defer_ok =
                                                              (uu___332_11333.defer_ok);
                                                            smt_ok =
                                                              (uu___332_11333.smt_ok);
                                                            tcenv =
                                                              (uu___332_11333.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11342 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11374 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11374 with
                                | (t1_base,p1_opt) ->
                                    let uu____11421 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11421 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11531 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11531
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
                                               let uu____11579 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11579
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
                                               let uu____11609 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11609
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
                                               let uu____11639 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11639
                                           | uu____11642 -> t_base  in
                                         let uu____11659 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11659 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11673 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11673, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11680 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11680 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11727 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11727 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11774 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11774
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
                              let uu____11798 = combine t11 t21 wl2  in
                              (match uu____11798 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11831 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11831
                                     then
                                       let uu____11832 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11832
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11871 ts1 =
               match uu____11871 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____11934 = pairwise out t wl2  in
                        (match uu____11934 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____11970 =
               let uu____11981 = FStar_List.hd ts  in (uu____11981, [], wl1)
                in
             let uu____11990 = FStar_List.tl ts  in
             aux uu____11970 uu____11990  in
           let uu____11997 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____11997 with
           | (this_flex,this_rigid) ->
               let uu____12021 =
                 let uu____12022 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12022.FStar_Syntax_Syntax.n  in
               (match uu____12021 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12043 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12043
                    then
                      let uu____12044 = destruct_flex_t this_flex wl  in
                      (match uu____12044 with
                       | (flex,wl1) ->
                           let uu____12051 = quasi_pattern env flex  in
                           (match uu____12051 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12069 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12069
                                  then
                                    let uu____12070 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12070
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12073 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___333_12076 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___333_12076.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___333_12076.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___333_12076.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___333_12076.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___333_12076.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___333_12076.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___333_12076.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___333_12076.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___333_12076.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12073)
                | uu____12077 ->
                    ((let uu____12079 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12079
                      then
                        let uu____12080 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12080
                      else ());
                     (let uu____12082 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12082 with
                      | (u,_args) ->
                          let uu____12119 =
                            let uu____12120 = FStar_Syntax_Subst.compress u
                               in
                            uu____12120.FStar_Syntax_Syntax.n  in
                          (match uu____12119 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12151 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12151 with
                                 | (u',uu____12167) ->
                                     let uu____12188 =
                                       let uu____12189 = whnf env u'  in
                                       uu____12189.FStar_Syntax_Syntax.n  in
                                     (match uu____12188 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12214 -> false)
                                  in
                               let uu____12215 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___298_12238  ->
                                         match uu___298_12238 with
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
                                              | uu____12247 -> false)
                                         | uu____12250 -> false))
                                  in
                               (match uu____12215 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12264 = whnf env this_rigid
                                         in
                                      let uu____12265 =
                                        FStar_List.collect
                                          (fun uu___299_12271  ->
                                             match uu___299_12271 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12277 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12277]
                                             | uu____12279 -> [])
                                          bounds_probs
                                         in
                                      uu____12264 :: uu____12265  in
                                    let uu____12280 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12280 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12311 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12326 =
                                               let uu____12327 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12327.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12326 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12339 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12339)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12348 -> bound  in
                                           let uu____12349 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12349)  in
                                         (match uu____12311 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12378 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12378
                                                then
                                                  let wl'1 =
                                                    let uu___334_12380 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___334_12380.wl_deferred);
                                                      ctr =
                                                        (uu___334_12380.ctr);
                                                      defer_ok =
                                                        (uu___334_12380.defer_ok);
                                                      smt_ok =
                                                        (uu___334_12380.smt_ok);
                                                      tcenv =
                                                        (uu___334_12380.tcenv);
                                                      wl_implicits =
                                                        (uu___334_12380.wl_implicits)
                                                    }  in
                                                  let uu____12381 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12381
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12384 =
                                                  solve_t env eq_prob
                                                    (let uu___335_12386 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___335_12386.wl_deferred);
                                                       ctr =
                                                         (uu___335_12386.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___335_12386.smt_ok);
                                                       tcenv =
                                                         (uu___335_12386.tcenv);
                                                       wl_implicits =
                                                         (uu___335_12386.wl_implicits)
                                                     })
                                                   in
                                                match uu____12384 with
                                                | Success uu____12387 ->
                                                    let wl2 =
                                                      let uu___336_12393 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___336_12393.wl_deferred);
                                                        ctr =
                                                          (uu___336_12393.ctr);
                                                        defer_ok =
                                                          (uu___336_12393.defer_ok);
                                                        smt_ok =
                                                          (uu___336_12393.smt_ok);
                                                        tcenv =
                                                          (uu___336_12393.tcenv);
                                                        wl_implicits =
                                                          (uu___336_12393.wl_implicits)
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
                                                    let uu____12408 =
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
                                                     (let uu____12420 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12420
                                                      then
                                                        let uu____12421 =
                                                          let uu____12422 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12422
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12421
                                                      else ());
                                                     (let uu____12428 =
                                                        let uu____12443 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12443)
                                                         in
                                                      match uu____12428 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12465))
                                                          ->
                                                          let uu____12490 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12490
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
                                                                 let uu____12507
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12507)))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
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
                                                                   let uu____12549
                                                                    =
                                                                    let uu____12554
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12554
                                                                     in
                                                                   solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12549
                                                                    [] wl2
                                                                    in
                                                                 let uu____12559
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12559)))
                                                      | uu____12560 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12575 when flip ->
                               let uu____12576 =
                                 let uu____12577 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12578 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12577 uu____12578
                                  in
                               failwith uu____12576
                           | uu____12579 ->
                               let uu____12580 =
                                 let uu____12581 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12582 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12581 uu____12582
                                  in
                               failwith uu____12580)))))

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
                      (fun uu____12610  ->
                         match uu____12610 with
                         | (x,i) ->
                             let uu____12621 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12621, i)) bs_lhs
                     in
                  let uu____12622 = lhs  in
                  match uu____12622 with
                  | (uu____12623,u_lhs,uu____12625) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12718 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12728 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12728, univ)
                             in
                          match uu____12718 with
                          | (k,univ) ->
                              let uu____12735 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12735 with
                               | (uu____12750,u,wl3) ->
                                   let uu____12753 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12753, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12779 =
                              let uu____12790 =
                                let uu____12799 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12799 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12842  ->
                                   fun uu____12843  ->
                                     match (uu____12842, uu____12843) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12922 =
                                           let uu____12929 =
                                             let uu____12932 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12932
                                              in
                                           copy_uvar u_lhs [] uu____12929 wl2
                                            in
                                         (match uu____12922 with
                                          | (uu____12957,t_a,wl3) ->
                                              let uu____12960 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____12960 with
                                               | (uu____12977,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12790
                                ([], wl1)
                               in
                            (match uu____12779 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___337_13019 = ct  in
                                   let uu____13020 =
                                     let uu____13023 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13023
                                      in
                                   let uu____13032 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___337_13019.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___337_13019.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13020;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13032;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___337_13019.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___338_13046 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___338_13046.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___338_13046.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13049 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13049 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13103 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13103 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13114 =
                                          let uu____13119 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13119)  in
                                        TERM uu____13114  in
                                      let uu____13120 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13120 with
                                       | (sub_prob,wl3) ->
                                           let uu____13131 =
                                             let uu____13132 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13132
                                              in
                                           solve env uu____13131))
                             | (x,imp)::formals2 ->
                                 let uu____13146 =
                                   let uu____13153 =
                                     let uu____13156 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13156
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13153 wl1
                                    in
                                 (match uu____13146 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13175 =
                                          let uu____13178 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13178
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13175 u_x
                                         in
                                      let uu____13179 =
                                        let uu____13182 =
                                          let uu____13185 =
                                            let uu____13186 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13186, imp)  in
                                          [uu____13185]  in
                                        FStar_List.append bs_terms
                                          uu____13182
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13179 formals2 wl2)
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
              (let uu____13228 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13228
               then
                 let uu____13229 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13230 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13229 (rel_to_string (p_rel orig)) uu____13230
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13335 = rhs wl1 scope env1 subst1  in
                     (match uu____13335 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13355 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13355
                            then
                              let uu____13356 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13356
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___339_13410 = hd1  in
                       let uu____13411 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___339_13410.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___339_13410.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13411
                       }  in
                     let hd21 =
                       let uu___340_13415 = hd2  in
                       let uu____13416 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___340_13415.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___340_13415.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13416
                       }  in
                     let uu____13419 =
                       let uu____13424 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13424
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13419 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13443 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13443
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13447 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13447 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13502 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13502
                                  in
                               ((let uu____13514 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13514
                                 then
                                   let uu____13515 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13516 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13515
                                     uu____13516
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13543 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13572 = aux wl [] env [] bs1 bs2  in
               match uu____13572 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13619 = attempt sub_probs wl2  in
                   solve env uu____13619)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13624 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13624 wl)

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
              let uu____13638 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13638 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13668 = lhs1  in
              match uu____13668 with
              | (uu____13671,ctx_u,uu____13673) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13679 ->
                        let uu____13680 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13680 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13727 = quasi_pattern env1 lhs1  in
              match uu____13727 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13757) ->
                  let uu____13762 = lhs1  in
                  (match uu____13762 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13776 = occurs_check ctx_u rhs1  in
                       (match uu____13776 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13818 =
                                let uu____13825 =
                                  let uu____13826 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13826
                                   in
                                FStar_Util.Inl uu____13825  in
                              (uu____13818, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13846 =
                                 let uu____13847 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13847  in
                               if uu____13846
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13867 =
                                    let uu____13874 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13874  in
                                  let uu____13879 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13867, uu____13879)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13941  ->
                     match uu____13941 with
                     | (x,i) ->
                         let uu____13952 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13952, i)) bs_lhs
                 in
              let uu____13953 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13953 with
              | (rhs_hd,args) ->
                  let uu____13990 = FStar_Util.prefix args  in
                  (match uu____13990 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14048 = lhs1  in
                       (match uu____14048 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14052 =
                              let uu____14063 =
                                let uu____14070 =
                                  let uu____14073 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14073
                                   in
                                copy_uvar u_lhs [] uu____14070 wl1  in
                              match uu____14063 with
                              | (uu____14098,t_last_arg,wl2) ->
                                  let uu____14101 =
                                    let uu____14108 =
                                      let uu____14109 =
                                        let uu____14116 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14116]  in
                                      FStar_List.append bs_lhs uu____14109
                                       in
                                    copy_uvar u_lhs uu____14108 t_res_lhs wl2
                                     in
                                  (match uu____14101 with
                                   | (uu____14143,lhs',wl3) ->
                                       let uu____14146 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14146 with
                                        | (uu____14163,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14052 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14184 =
                                     let uu____14185 =
                                       let uu____14190 =
                                         let uu____14191 =
                                           let uu____14194 =
                                             let uu____14199 =
                                               let uu____14200 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14200]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14199
                                              in
                                           uu____14194
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14191
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14190)  in
                                     TERM uu____14185  in
                                   [uu____14184]  in
                                 let uu____14221 =
                                   let uu____14228 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14228 with
                                   | (p1,wl3) ->
                                       let uu____14245 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14245 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14221 with
                                  | (sub_probs,wl3) ->
                                      let uu____14272 =
                                        let uu____14273 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14273  in
                                      solve env1 uu____14272))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14306 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14306 with
                | (uu____14321,args) ->
                    (match args with | [] -> false | uu____14349 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14364 =
                  let uu____14365 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14365.FStar_Syntax_Syntax.n  in
                match uu____14364 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14368 -> true
                | uu____14381 -> false  in
              let uu____14382 = quasi_pattern env1 lhs1  in
              match uu____14382 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14393 =
                    let uu____14394 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14394
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14393
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14401 = is_app rhs1  in
                  if uu____14401
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14403 = is_arrow rhs1  in
                     if uu____14403
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14405 =
                          let uu____14406 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14406
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14405))
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
                let uu____14409 = lhs  in
                (match uu____14409 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14413 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14413 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14428 =
                              let uu____14431 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14431
                               in
                            FStar_All.pipe_right uu____14428
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14446 = occurs_check ctx_uv rhs1  in
                          (match uu____14446 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14468 =
                                   let uu____14469 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14469
                                    in
                                 giveup_or_defer env orig wl uu____14468
                               else
                                 (let uu____14471 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14471
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14476 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14476
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14478 =
                                         let uu____14479 =
                                           names_to_string1 fvs2  in
                                         let uu____14480 =
                                           names_to_string1 fvs1  in
                                         let uu____14481 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14479 uu____14480
                                           uu____14481
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14478)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14487 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14491 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14491 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14514 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14514
                             | (FStar_Util.Inl msg,uu____14516) ->
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
                  (let uu____14545 =
                     let uu____14562 = quasi_pattern env lhs  in
                     let uu____14569 = quasi_pattern env rhs  in
                     (uu____14562, uu____14569)  in
                   match uu____14545 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14612 = lhs  in
                       (match uu____14612 with
                        | ({ FStar_Syntax_Syntax.n = uu____14613;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14615;_},u_lhs,uu____14617)
                            ->
                            let uu____14620 = rhs  in
                            (match uu____14620 with
                             | (uu____14621,u_rhs,uu____14623) ->
                                 let uu____14624 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14624
                                 then
                                   let uu____14625 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14625
                                 else
                                   (let uu____14627 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14627 with
                                    | (sub_prob,wl1) ->
                                        let uu____14638 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14638 with
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
                                             let uu____14666 =
                                               let uu____14673 =
                                                 let uu____14676 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14676
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
                                                 uu____14673
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14666 with
                                              | (uu____14679,w,wl2) ->
                                                  let w_app =
                                                    let uu____14685 =
                                                      let uu____14690 =
                                                        FStar_List.map
                                                          (fun uu____14699 
                                                             ->
                                                             match uu____14699
                                                             with
                                                             | (z,uu____14705)
                                                                 ->
                                                                 let uu____14706
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14706)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14690
                                                       in
                                                    uu____14685
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14710 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14710
                                                    then
                                                      let uu____14711 =
                                                        let uu____14714 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14715 =
                                                          let uu____14718 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14719 =
                                                            let uu____14722 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14723 =
                                                              let uu____14726
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14731
                                                                =
                                                                let uu____14734
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14739
                                                                  =
                                                                  let uu____14742
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14742]
                                                                   in
                                                                uu____14734
                                                                  ::
                                                                  uu____14739
                                                                 in
                                                              uu____14726 ::
                                                                uu____14731
                                                               in
                                                            uu____14722 ::
                                                              uu____14723
                                                             in
                                                          uu____14718 ::
                                                            uu____14719
                                                           in
                                                        uu____14714 ::
                                                          uu____14715
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14711
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14748 =
                                                          let uu____14753 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14753)
                                                           in
                                                        TERM uu____14748  in
                                                      let uu____14754 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14754
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14759 =
                                                             let uu____14764
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
                                                               uu____14764)
                                                              in
                                                           TERM uu____14759
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14765 =
                                                      let uu____14766 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14766
                                                       in
                                                    solve env uu____14765)))))))
                   | uu____14767 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14831 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14831
            then
              let uu____14832 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14833 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14834 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14835 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14832 uu____14833 uu____14834 uu____14835
            else ());
           (let uu____14839 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14839
            then
              let uu____14840 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14841 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14842 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14843 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14840 uu____14841 uu____14842 uu____14843
            else ());
           (let uu____14845 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14845 with
            | (head1,args1) ->
                let uu____14882 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14882 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____14936 =
                         let uu____14937 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14938 = args_to_string args1  in
                         let uu____14939 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____14940 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____14937 uu____14938 uu____14939 uu____14940
                          in
                       giveup env1 uu____14936 orig
                     else
                       (let uu____14942 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____14948 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____14948 = FStar_Syntax_Util.Equal)
                           in
                        if uu____14942
                        then
                          let uu____14949 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____14949 with
                          | USolved wl2 ->
                              let uu____14951 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____14951
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____14955 = base_and_refinement env1 t1  in
                           match uu____14955 with
                           | (base1,refinement1) ->
                               let uu____14980 = base_and_refinement env1 t2
                                  in
                               (match uu____14980 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15037 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15037 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15041 =
                                                FStar_List.fold_right2
                                                  (fun uu____15074  ->
                                                     fun uu____15075  ->
                                                       fun uu____15076  ->
                                                         match (uu____15074,
                                                                 uu____15075,
                                                                 uu____15076)
                                                         with
                                                         | ((a,uu____15112),
                                                            (a',uu____15114),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15135
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15135
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15041 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15163 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15163
                                                     then
                                                       let uu____15164 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15164
                                                     else ());
                                                    FStar_List.iter
                                                      (def_check_prob
                                                         "solve_t' subprobs")
                                                      subprobs;
                                                    (let formula =
                                                       let uu____15170 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15170
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     let uu____15178 =
                                                       attempt subprobs wl4
                                                        in
                                                     solve env1 uu____15178))))
                                     | uu____15179 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___341_15219 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___341_15219.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___341_15219.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___341_15219.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___341_15219.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___341_15219.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___341_15219.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___341_15219.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___341_15219.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15257 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15257
            then
              let uu____15258 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15259 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15260 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15261 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15258 uu____15259 uu____15260 uu____15261
            else ());
           (let uu____15263 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15263 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15294,uu____15295) ->
                     let rec may_relate head3 =
                       let uu____15322 =
                         let uu____15323 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15323.FStar_Syntax_Syntax.n  in
                       match uu____15322 with
                       | FStar_Syntax_Syntax.Tm_name uu____15326 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15327 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15350;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15351;
                             FStar_Syntax_Syntax.fv_qual = uu____15352;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15355;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15356;
                             FStar_Syntax_Syntax.fv_qual = uu____15357;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15361,uu____15362) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15404) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15410) ->
                           may_relate t
                       | uu____15415 -> false  in
                     let uu____15416 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15416
                     then
                       let uu____15417 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15417 with
                        | (guard,wl2) ->
                            let uu____15424 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15424)
                     else
                       (let uu____15426 =
                          let uu____15427 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15428 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15427 uu____15428
                           in
                        giveup env1 uu____15426 orig)
                 | (HeadMatch (true ),uu____15429) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____15442 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15442 with
                        | (guard,wl2) ->
                            let uu____15449 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15449)
                     else
                       (let uu____15451 =
                          let uu____15452 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____15453 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____15452 uu____15453
                           in
                        giveup env1 uu____15451 orig)
                 | (uu____15454,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___342_15468 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___342_15468.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___342_15468.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___342_15468.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___342_15468.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___342_15468.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___342_15468.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___342_15468.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___342_15468.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15492 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15492
          then
            let uu____15493 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15493
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15498 =
                let uu____15501 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15501  in
              def_check_closed_in (p_loc orig) "ref.t1" uu____15498 t1);
             (let uu____15513 =
                let uu____15516 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15516  in
              def_check_closed_in (p_loc orig) "ref.t2" uu____15513 t2);
             (let uu____15528 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15528
              then
                let uu____15529 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15530 =
                  let uu____15531 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15532 =
                    let uu____15533 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15533  in
                  Prims.strcat uu____15531 uu____15532  in
                let uu____15534 =
                  let uu____15535 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15536 =
                    let uu____15537 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15537  in
                  Prims.strcat uu____15535 uu____15536  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15529
                  uu____15530 uu____15534
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15540,uu____15541) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15566,FStar_Syntax_Syntax.Tm_delayed uu____15567) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15592,uu____15593) ->
                  let uu____15620 =
                    let uu___343_15621 = problem  in
                    let uu____15622 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___343_15621.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15622;
                      FStar_TypeChecker_Common.relation =
                        (uu___343_15621.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___343_15621.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___343_15621.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___343_15621.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___343_15621.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___343_15621.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___343_15621.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___343_15621.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15620 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____15623,uu____15624) ->
                  let uu____15631 =
                    let uu___344_15632 = problem  in
                    let uu____15633 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___344_15632.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15633;
                      FStar_TypeChecker_Common.relation =
                        (uu___344_15632.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___344_15632.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___344_15632.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___344_15632.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___344_15632.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___344_15632.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___344_15632.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___344_15632.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15631 wl
              | (uu____15634,FStar_Syntax_Syntax.Tm_ascribed uu____15635) ->
                  let uu____15662 =
                    let uu___345_15663 = problem  in
                    let uu____15664 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___345_15663.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___345_15663.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___345_15663.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15664;
                      FStar_TypeChecker_Common.element =
                        (uu___345_15663.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___345_15663.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___345_15663.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___345_15663.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___345_15663.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___345_15663.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15662 wl
              | (uu____15665,FStar_Syntax_Syntax.Tm_meta uu____15666) ->
                  let uu____15673 =
                    let uu___346_15674 = problem  in
                    let uu____15675 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___346_15674.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___346_15674.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___346_15674.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15675;
                      FStar_TypeChecker_Common.element =
                        (uu___346_15674.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___346_15674.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___346_15674.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___346_15674.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___346_15674.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___346_15674.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15673 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15677),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15679)) ->
                  let uu____15688 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15688
              | (FStar_Syntax_Syntax.Tm_bvar uu____15689,uu____15690) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15691,FStar_Syntax_Syntax.Tm_bvar uu____15692) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___300_15751 =
                    match uu___300_15751 with
                    | [] -> c
                    | bs ->
                        let uu____15773 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15773
                     in
                  let uu____15782 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15782 with
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
                                    let uu____15905 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15905
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
                  let mk_t t l uu___301_15980 =
                    match uu___301_15980 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____16014 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____16014 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16133 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16134 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16133
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16134 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16135,uu____16136) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16163 -> true
                    | uu____16180 -> false  in
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
                      (let uu____16233 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___347_16241 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___347_16241.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___347_16241.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___347_16241.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___347_16241.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___347_16241.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___347_16241.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___347_16241.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___347_16241.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___347_16241.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___347_16241.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___347_16241.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___347_16241.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___347_16241.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___347_16241.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___347_16241.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___347_16241.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___347_16241.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___347_16241.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___347_16241.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___347_16241.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___347_16241.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___347_16241.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___347_16241.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___347_16241.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___347_16241.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___347_16241.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___347_16241.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___347_16241.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___347_16241.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___347_16241.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___347_16241.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___347_16241.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___347_16241.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___347_16241.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___347_16241.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___347_16241.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16233 with
                       | (uu____16244,ty,uu____16246) ->
                           let uu____16247 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16247)
                     in
                  let uu____16248 =
                    let uu____16265 = maybe_eta t1  in
                    let uu____16272 = maybe_eta t2  in
                    (uu____16265, uu____16272)  in
                  (match uu____16248 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___348_16314 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___348_16314.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___348_16314.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___348_16314.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___348_16314.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___348_16314.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___348_16314.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___348_16314.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___348_16314.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16335 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16335
                       then
                         let uu____16336 = destruct_flex_t not_abs wl  in
                         (match uu____16336 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16351 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16351.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16351.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16351.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16351.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16351.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16351.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16351.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16351.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16373 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16373
                       then
                         let uu____16374 = destruct_flex_t not_abs wl  in
                         (match uu____16374 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16389 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16389.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16389.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16389.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16389.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16389.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16389.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16389.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16389.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16391 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16408,FStar_Syntax_Syntax.Tm_abs uu____16409) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16436 -> true
                    | uu____16453 -> false  in
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
                      (let uu____16506 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___347_16514 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___347_16514.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___347_16514.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___347_16514.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___347_16514.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___347_16514.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___347_16514.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___347_16514.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___347_16514.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___347_16514.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___347_16514.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___347_16514.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___347_16514.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___347_16514.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___347_16514.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___347_16514.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___347_16514.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___347_16514.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___347_16514.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___347_16514.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___347_16514.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___347_16514.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___347_16514.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___347_16514.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___347_16514.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___347_16514.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___347_16514.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___347_16514.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___347_16514.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___347_16514.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___347_16514.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___347_16514.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___347_16514.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___347_16514.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___347_16514.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___347_16514.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___347_16514.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16506 with
                       | (uu____16517,ty,uu____16519) ->
                           let uu____16520 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16520)
                     in
                  let uu____16521 =
                    let uu____16538 = maybe_eta t1  in
                    let uu____16545 = maybe_eta t2  in
                    (uu____16538, uu____16545)  in
                  (match uu____16521 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___348_16587 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___348_16587.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___348_16587.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___348_16587.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___348_16587.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___348_16587.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___348_16587.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___348_16587.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___348_16587.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16608 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16608
                       then
                         let uu____16609 = destruct_flex_t not_abs wl  in
                         (match uu____16609 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16624 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16624.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16624.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16624.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16624.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16624.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16624.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16624.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16624.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16646 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16646
                       then
                         let uu____16647 = destruct_flex_t not_abs wl  in
                         (match uu____16647 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___349_16662 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___349_16662.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___349_16662.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___349_16662.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___349_16662.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___349_16662.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___349_16662.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___349_16662.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___349_16662.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16664 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16696 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16696) &&
                       (let uu____16700 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16700))
                      &&
                      (let uu____16707 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16707 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___302_16719 =
                             match uu___302_16719 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16720 -> true
                             | uu____16721 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16722 -> false)
                     in
                  let uu____16723 = as_refinement should_delta env wl t1  in
                  (match uu____16723 with
                   | (x11,phi1) ->
                       let uu____16736 = as_refinement should_delta env wl t2
                          in
                       (match uu____16736 with
                        | (x21,phi21) ->
                            let uu____16749 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16749 with
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
                                   let uu____16815 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16815
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16827 =
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
                                   (let uu____16838 =
                                      let uu____16841 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16841
                                       in
                                    def_check_closed_in (p_loc orig) "ref.1"
                                      uu____16838 (p_guard base_prob));
                                   (let uu____16853 =
                                      let uu____16856 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16856
                                       in
                                    def_check_closed_in (p_loc orig) "ref.2"
                                      uu____16853 impl);
                                   (let wl2 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl1
                                       in
                                    let uu____16868 = attempt [base_prob] wl2
                                       in
                                    solve env1 uu____16868)
                                    in
                                 let has_uvars =
                                   (let uu____16872 =
                                      let uu____16873 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16873  in
                                    Prims.op_Negation uu____16872) ||
                                     (let uu____16877 =
                                        let uu____16878 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16878
                                         in
                                      Prims.op_Negation uu____16877)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16881 =
                                     let uu____16886 =
                                       let uu____16887 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16887]  in
                                     mk_t_problem wl1 uu____16886 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16881 with
                                    | (ref_prob,wl2) ->
                                        let uu____16902 =
                                          solve env1
                                            (let uu___350_16904 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___350_16904.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___350_16904.smt_ok);
                                               tcenv = (uu___350_16904.tcenv);
                                               wl_implicits =
                                                 (uu___350_16904.wl_implicits)
                                             })
                                           in
                                        (match uu____16902 with
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
                                         | Success uu____16914 ->
                                             let guard =
                                               let uu____16922 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16922
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___351_16931 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___351_16931.attempting);
                                                 wl_deferred =
                                                   (uu___351_16931.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___351_16931.defer_ok);
                                                 smt_ok =
                                                   (uu___351_16931.smt_ok);
                                                 tcenv =
                                                   (uu___351_16931.tcenv);
                                                 wl_implicits =
                                                   (uu___351_16931.wl_implicits)
                                               }  in
                                             let uu____16932 =
                                               attempt [base_prob] wl4  in
                                             solve env1 uu____16932))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16934,FStar_Syntax_Syntax.Tm_uvar uu____16935) ->
                  let uu____16964 = destruct_flex_t t1 wl  in
                  (match uu____16964 with
                   | (f1,wl1) ->
                       let uu____16971 = destruct_flex_t t2 wl1  in
                       (match uu____16971 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16978;
                    FStar_Syntax_Syntax.pos = uu____16979;
                    FStar_Syntax_Syntax.vars = uu____16980;_},uu____16981),FStar_Syntax_Syntax.Tm_uvar
                 uu____16982) ->
                  let uu____17031 = destruct_flex_t t1 wl  in
                  (match uu____17031 with
                   | (f1,wl1) ->
                       let uu____17038 = destruct_flex_t t2 wl1  in
                       (match uu____17038 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17045,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17046;
                    FStar_Syntax_Syntax.pos = uu____17047;
                    FStar_Syntax_Syntax.vars = uu____17048;_},uu____17049))
                  ->
                  let uu____17098 = destruct_flex_t t1 wl  in
                  (match uu____17098 with
                   | (f1,wl1) ->
                       let uu____17105 = destruct_flex_t t2 wl1  in
                       (match uu____17105 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17112;
                    FStar_Syntax_Syntax.pos = uu____17113;
                    FStar_Syntax_Syntax.vars = uu____17114;_},uu____17115),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17116;
                    FStar_Syntax_Syntax.pos = uu____17117;
                    FStar_Syntax_Syntax.vars = uu____17118;_},uu____17119))
                  ->
                  let uu____17188 = destruct_flex_t t1 wl  in
                  (match uu____17188 with
                   | (f1,wl1) ->
                       let uu____17195 = destruct_flex_t t2 wl1  in
                       (match uu____17195 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____17202,uu____17203) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17218 = destruct_flex_t t1 wl  in
                  (match uu____17218 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17225;
                    FStar_Syntax_Syntax.pos = uu____17226;
                    FStar_Syntax_Syntax.vars = uu____17227;_},uu____17228),uu____17229)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17264 = destruct_flex_t t1 wl  in
                  (match uu____17264 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17271,FStar_Syntax_Syntax.Tm_uvar uu____17272) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17287,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17288;
                    FStar_Syntax_Syntax.pos = uu____17289;
                    FStar_Syntax_Syntax.vars = uu____17290;_},uu____17291))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17326,FStar_Syntax_Syntax.Tm_arrow uu____17327) ->
                  solve_t' env
                    (let uu___352_17355 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___352_17355.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___352_17355.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___352_17355.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___352_17355.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___352_17355.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___352_17355.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___352_17355.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___352_17355.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___352_17355.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17356;
                    FStar_Syntax_Syntax.pos = uu____17357;
                    FStar_Syntax_Syntax.vars = uu____17358;_},uu____17359),FStar_Syntax_Syntax.Tm_arrow
                 uu____17360) ->
                  solve_t' env
                    (let uu___352_17408 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___352_17408.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___352_17408.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___352_17408.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___352_17408.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___352_17408.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___352_17408.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___352_17408.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___352_17408.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___352_17408.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17409,FStar_Syntax_Syntax.Tm_uvar uu____17410) ->
                  let uu____17425 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17425
              | (uu____17426,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17427;
                    FStar_Syntax_Syntax.pos = uu____17428;
                    FStar_Syntax_Syntax.vars = uu____17429;_},uu____17430))
                  ->
                  let uu____17465 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17465
              | (FStar_Syntax_Syntax.Tm_uvar uu____17466,uu____17467) ->
                  let uu____17482 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17482
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17483;
                    FStar_Syntax_Syntax.pos = uu____17484;
                    FStar_Syntax_Syntax.vars = uu____17485;_},uu____17486),uu____17487)
                  ->
                  let uu____17522 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17522
              | (FStar_Syntax_Syntax.Tm_refine uu____17523,uu____17524) ->
                  let t21 =
                    let uu____17532 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17532  in
                  solve_t env
                    (let uu___353_17558 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___353_17558.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___353_17558.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___353_17558.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___353_17558.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___353_17558.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___353_17558.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___353_17558.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___353_17558.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___353_17558.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17559,FStar_Syntax_Syntax.Tm_refine uu____17560) ->
                  let t11 =
                    let uu____17568 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17568  in
                  solve_t env
                    (let uu___354_17594 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___354_17594.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___354_17594.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___354_17594.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___354_17594.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___354_17594.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___354_17594.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___354_17594.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___354_17594.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___354_17594.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17676 =
                    let uu____17677 = guard_of_prob env wl problem t1 t2  in
                    match uu____17677 with
                    | (guard,wl1) ->
                        let uu____17684 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17684
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____17895 = br1  in
                        (match uu____17895 with
                         | (p1,w1,uu____17920) ->
                             let uu____17937 = br2  in
                             (match uu____17937 with
                              | (p2,w2,uu____17956) ->
                                  let uu____17961 =
                                    let uu____17962 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____17962  in
                                  if uu____17961
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____17978 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____17978 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____18011 = br2  in
                                         (match uu____18011 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____18040 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____18040
                                                 in
                                              let uu____18045 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____18068,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____18085) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____18128 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____18128 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____18045
                                                (fun uu____18170  ->
                                                   match uu____18170 with
                                                   | (wprobs,wl2) ->
                                                       let uu____18191 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____18191
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____18206 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____18206
                                                              (fun
                                                                 uu____18230 
                                                                 ->
                                                                 match uu____18230
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18315 -> FStar_Pervasives_Native.None  in
                  let uu____18352 = solve_branches wl brs1 brs2  in
                  (match uu____18352 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18380 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18380 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18397 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18397  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18406 =
                              let uu____18407 =
                                attempt sub_probs1
                                  (let uu___355_18409 = wl3  in
                                   {
                                     attempting = (uu___355_18409.attempting);
                                     wl_deferred =
                                       (uu___355_18409.wl_deferred);
                                     ctr = (uu___355_18409.ctr);
                                     defer_ok = (uu___355_18409.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___355_18409.tcenv);
                                     wl_implicits =
                                       (uu___355_18409.wl_implicits)
                                   })
                                 in
                              solve env uu____18407  in
                            (match uu____18406 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____18413 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____18419,uu____18420) ->
                  let head1 =
                    let uu____18444 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18444
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18484 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18484
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18524 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18524
                    then
                      let uu____18525 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18526 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18527 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18525 uu____18526 uu____18527
                    else ());
                   (let uu____18529 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18529
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18536 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18536
                       then
                         let uu____18537 =
                           let uu____18544 =
                             let uu____18545 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18545 = FStar_Syntax_Util.Equal  in
                           if uu____18544
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18555 = mk_eq2 wl orig t1 t2  in
                              match uu____18555 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18537 with
                         | (guard,wl1) ->
                             let uu____18576 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18576
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18579,uu____18580) ->
                  let head1 =
                    let uu____18588 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18588
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18628 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18628
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18668 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18668
                    then
                      let uu____18669 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18670 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18671 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18669 uu____18670 uu____18671
                    else ());
                   (let uu____18673 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18673
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18680 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18680
                       then
                         let uu____18681 =
                           let uu____18688 =
                             let uu____18689 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18689 = FStar_Syntax_Util.Equal  in
                           if uu____18688
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18699 = mk_eq2 wl orig t1 t2  in
                              match uu____18699 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18681 with
                         | (guard,wl1) ->
                             let uu____18720 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18720
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18723,uu____18724) ->
                  let head1 =
                    let uu____18726 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18726
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18766 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18766
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18806 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18806
                    then
                      let uu____18807 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18808 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18809 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18807 uu____18808 uu____18809
                    else ());
                   (let uu____18811 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18811
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18818 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18818
                       then
                         let uu____18819 =
                           let uu____18826 =
                             let uu____18827 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18827 = FStar_Syntax_Util.Equal  in
                           if uu____18826
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18837 = mk_eq2 wl orig t1 t2  in
                              match uu____18837 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18819 with
                         | (guard,wl1) ->
                             let uu____18858 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18858
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18861,uu____18862) ->
                  let head1 =
                    let uu____18864 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18864
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18904 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18904
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18944 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18944
                    then
                      let uu____18945 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18946 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18947 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18945 uu____18946 uu____18947
                    else ());
                   (let uu____18949 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18949
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18956 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18956
                       then
                         let uu____18957 =
                           let uu____18964 =
                             let uu____18965 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18965 = FStar_Syntax_Util.Equal  in
                           if uu____18964
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18975 = mk_eq2 wl orig t1 t2  in
                              match uu____18975 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18957 with
                         | (guard,wl1) ->
                             let uu____18996 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18996
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18999,uu____19000) ->
                  let head1 =
                    let uu____19002 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19002
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19042 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19042
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19082 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19082
                    then
                      let uu____19083 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19084 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19085 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19083 uu____19084 uu____19085
                    else ());
                   (let uu____19087 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19087
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19094 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19094
                       then
                         let uu____19095 =
                           let uu____19102 =
                             let uu____19103 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19103 = FStar_Syntax_Util.Equal  in
                           if uu____19102
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19113 = mk_eq2 wl orig t1 t2  in
                              match uu____19113 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19095 with
                         | (guard,wl1) ->
                             let uu____19134 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19134
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____19137,uu____19138) ->
                  let head1 =
                    let uu____19154 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19154
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19194 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19194
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19234 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19234
                    then
                      let uu____19235 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19236 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19237 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19235 uu____19236 uu____19237
                    else ());
                   (let uu____19239 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19239
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19246 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19246
                       then
                         let uu____19247 =
                           let uu____19254 =
                             let uu____19255 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19255 = FStar_Syntax_Util.Equal  in
                           if uu____19254
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19265 = mk_eq2 wl orig t1 t2  in
                              match uu____19265 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19247 with
                         | (guard,wl1) ->
                             let uu____19286 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19286
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19289,FStar_Syntax_Syntax.Tm_match uu____19290) ->
                  let head1 =
                    let uu____19314 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19314
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19354 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19354
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19394 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19394
                    then
                      let uu____19395 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19396 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19397 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19395 uu____19396 uu____19397
                    else ());
                   (let uu____19399 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19399
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19406 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19406
                       then
                         let uu____19407 =
                           let uu____19414 =
                             let uu____19415 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19415 = FStar_Syntax_Util.Equal  in
                           if uu____19414
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19425 = mk_eq2 wl orig t1 t2  in
                              match uu____19425 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19407 with
                         | (guard,wl1) ->
                             let uu____19446 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19446
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19449,FStar_Syntax_Syntax.Tm_uinst uu____19450) ->
                  let head1 =
                    let uu____19458 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19458
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19498 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19498
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19538 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19538
                    then
                      let uu____19539 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19540 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19541 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19539 uu____19540 uu____19541
                    else ());
                   (let uu____19543 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19543
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19550 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19550
                       then
                         let uu____19551 =
                           let uu____19558 =
                             let uu____19559 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19559 = FStar_Syntax_Util.Equal  in
                           if uu____19558
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19569 = mk_eq2 wl orig t1 t2  in
                              match uu____19569 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19551 with
                         | (guard,wl1) ->
                             let uu____19590 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19590
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19593,FStar_Syntax_Syntax.Tm_name uu____19594) ->
                  let head1 =
                    let uu____19596 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19596
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19636 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19636
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19676 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19676
                    then
                      let uu____19677 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19678 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19679 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19677 uu____19678 uu____19679
                    else ());
                   (let uu____19681 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19681
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19688 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19688
                       then
                         let uu____19689 =
                           let uu____19696 =
                             let uu____19697 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19697 = FStar_Syntax_Util.Equal  in
                           if uu____19696
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19707 = mk_eq2 wl orig t1 t2  in
                              match uu____19707 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19689 with
                         | (guard,wl1) ->
                             let uu____19728 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19728
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19731,FStar_Syntax_Syntax.Tm_constant uu____19732) ->
                  let head1 =
                    let uu____19734 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19734
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19768 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19768
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
              | (uu____19857,FStar_Syntax_Syntax.Tm_fvar uu____19858) ->
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
              | (uu____19983,FStar_Syntax_Syntax.Tm_app uu____19984) ->
                  let head1 =
                    let uu____20000 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20000
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20034 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20034
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20074 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20074
                    then
                      let uu____20075 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20076 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20077 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20075 uu____20076 uu____20077
                    else ());
                   (let uu____20079 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20079
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20086 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20086
                       then
                         let uu____20087 =
                           let uu____20094 =
                             let uu____20095 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20095 = FStar_Syntax_Util.Equal  in
                           if uu____20094
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20105 = mk_eq2 wl orig t1 t2  in
                              match uu____20105 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20087 with
                         | (guard,wl1) ->
                             let uu____20126 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20126
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____20129,FStar_Syntax_Syntax.Tm_let uu____20130) ->
                  let uu____20155 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____20155
                  then
                    let uu____20156 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____20156
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____20158,uu____20159) ->
                  let uu____20172 =
                    let uu____20177 =
                      let uu____20178 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20179 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20180 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20181 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20178 uu____20179 uu____20180 uu____20181
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20177)
                     in
                  FStar_Errors.raise_error uu____20172
                    t1.FStar_Syntax_Syntax.pos
              | (uu____20182,FStar_Syntax_Syntax.Tm_let uu____20183) ->
                  let uu____20196 =
                    let uu____20201 =
                      let uu____20202 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20203 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20204 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20205 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20202 uu____20203 uu____20204 uu____20205
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20201)
                     in
                  FStar_Errors.raise_error uu____20196
                    t1.FStar_Syntax_Syntax.pos
              | uu____20206 -> giveup env "head tag mismatch" orig))))

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
          (let uu____20265 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20265
           then
             let uu____20266 =
               let uu____20267 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____20267  in
             let uu____20268 =
               let uu____20269 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____20269  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____20266 uu____20268
           else ());
          (let uu____20271 =
             let uu____20272 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____20272  in
           if uu____20271
           then
             let uu____20273 =
               let uu____20274 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20275 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20274 uu____20275
                in
             giveup env uu____20273 orig
           else
             (let uu____20277 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____20277 with
              | (ret_sub_prob,wl1) ->
                  let uu____20284 =
                    FStar_List.fold_right2
                      (fun uu____20317  ->
                         fun uu____20318  ->
                           fun uu____20319  ->
                             match (uu____20317, uu____20318, uu____20319)
                             with
                             | ((a1,uu____20355),(a2,uu____20357),(arg_sub_probs,wl2))
                                 ->
                                 let uu____20378 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____20378 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____20284 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____20407 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____20407  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____20415 = attempt sub_probs wl3  in
                       solve env uu____20415)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20438 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20441)::[] -> wp1
              | uu____20458 ->
                  let uu____20467 =
                    let uu____20468 =
                      let uu____20469 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20469  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20468
                     in
                  failwith uu____20467
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20475 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20475]
              | x -> x  in
            let uu____20477 =
              let uu____20486 =
                let uu____20493 =
                  let uu____20494 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20494 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20493  in
              [uu____20486]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20477;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20507 = lift_c1 ()  in solve_eq uu____20507 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___303_20513  ->
                       match uu___303_20513 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20514 -> false))
                in
             let uu____20515 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20541)::uu____20542,(wp2,uu____20544)::uu____20545)
                   -> (wp1, wp2)
               | uu____20598 ->
                   let uu____20619 =
                     let uu____20624 =
                       let uu____20625 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20626 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20625 uu____20626
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20624)
                      in
                   FStar_Errors.raise_error uu____20619
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20515 with
             | (wpc1,wpc2) ->
                 let uu____20633 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20633
                 then
                   let uu____20636 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20636 wl
                 else
                   (let uu____20638 =
                      let uu____20645 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20645  in
                    match uu____20638 with
                    | (c2_decl,qualifiers) ->
                        let uu____20666 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20666
                        then
                          let c1_repr =
                            let uu____20670 =
                              let uu____20671 =
                                let uu____20672 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20672  in
                              let uu____20673 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20671 uu____20673
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20670
                             in
                          let c2_repr =
                            let uu____20675 =
                              let uu____20676 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20677 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20676 uu____20677
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20675
                             in
                          let uu____20678 =
                            let uu____20683 =
                              let uu____20684 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20685 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20684 uu____20685
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20683
                             in
                          (match uu____20678 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____20689 = attempt [prob] wl2  in
                               solve env uu____20689)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20700 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20700
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20703 =
                                     let uu____20710 =
                                       let uu____20711 =
                                         let uu____20726 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20729 =
                                           let uu____20738 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20745 =
                                             let uu____20754 =
                                               let uu____20761 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20761
                                                in
                                             [uu____20754]  in
                                           uu____20738 :: uu____20745  in
                                         (uu____20726, uu____20729)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20711
                                        in
                                     FStar_Syntax_Syntax.mk uu____20710  in
                                   uu____20703 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20802 =
                                    let uu____20809 =
                                      let uu____20810 =
                                        let uu____20825 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20828 =
                                          let uu____20837 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20844 =
                                            let uu____20853 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20860 =
                                              let uu____20869 =
                                                let uu____20876 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20876
                                                 in
                                              [uu____20869]  in
                                            uu____20853 :: uu____20860  in
                                          uu____20837 :: uu____20844  in
                                        (uu____20825, uu____20828)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20810
                                       in
                                    FStar_Syntax_Syntax.mk uu____20809  in
                                  uu____20802 FStar_Pervasives_Native.None r)
                              in
                           let uu____20920 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20920 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20928 =
                                   let uu____20931 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____20931
                                    in
                                 solve_prob orig uu____20928 [] wl1  in
                               let uu____20934 = attempt [base_prob] wl2  in
                               solve env uu____20934)))
           in
        let uu____20935 = FStar_Util.physical_equality c1 c2  in
        if uu____20935
        then
          let uu____20936 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20936
        else
          ((let uu____20939 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20939
            then
              let uu____20940 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20941 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20940
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20941
            else ());
           (let uu____20943 =
              let uu____20952 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20955 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20952, uu____20955)  in
            match uu____20943 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20973),FStar_Syntax_Syntax.Total
                    (t2,uu____20975)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____20992 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20992 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20993,FStar_Syntax_Syntax.Total uu____20994) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21012),FStar_Syntax_Syntax.Total
                    (t2,uu____21014)) ->
                     let uu____21031 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21031 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21033),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21035)) ->
                     let uu____21052 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21052 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21054),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21056)) ->
                     let uu____21073 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21073 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21074,FStar_Syntax_Syntax.Comp uu____21075) ->
                     let uu____21084 =
                       let uu___356_21087 = problem  in
                       let uu____21090 =
                         let uu____21091 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21091
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___356_21087.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21090;
                         FStar_TypeChecker_Common.relation =
                           (uu___356_21087.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___356_21087.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___356_21087.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___356_21087.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___356_21087.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___356_21087.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___356_21087.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___356_21087.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21084 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21092,FStar_Syntax_Syntax.Comp uu____21093) ->
                     let uu____21102 =
                       let uu___356_21105 = problem  in
                       let uu____21108 =
                         let uu____21109 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21109
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___356_21105.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21108;
                         FStar_TypeChecker_Common.relation =
                           (uu___356_21105.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___356_21105.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___356_21105.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___356_21105.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___356_21105.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___356_21105.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___356_21105.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___356_21105.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21102 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21110,FStar_Syntax_Syntax.GTotal uu____21111) ->
                     let uu____21120 =
                       let uu___357_21123 = problem  in
                       let uu____21126 =
                         let uu____21127 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21127
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___357_21123.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___357_21123.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___357_21123.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21126;
                         FStar_TypeChecker_Common.element =
                           (uu___357_21123.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___357_21123.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___357_21123.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___357_21123.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___357_21123.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___357_21123.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21120 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21128,FStar_Syntax_Syntax.Total uu____21129) ->
                     let uu____21138 =
                       let uu___357_21141 = problem  in
                       let uu____21144 =
                         let uu____21145 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21145
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___357_21141.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___357_21141.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___357_21141.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21144;
                         FStar_TypeChecker_Common.element =
                           (uu___357_21141.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___357_21141.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___357_21141.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___357_21141.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___357_21141.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___357_21141.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21138 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21146,FStar_Syntax_Syntax.Comp uu____21147) ->
                     let uu____21148 =
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
                     if uu____21148
                     then
                       let uu____21149 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21149 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21153 =
                            let uu____21158 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____21158
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21164 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21165 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21164, uu____21165))
                             in
                          match uu____21153 with
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
                           (let uu____21172 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21172
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21174 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21174 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21177 =
                                  let uu____21178 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21179 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21178 uu____21179
                                   in
                                giveup env uu____21177 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21186 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21214  ->
              match uu____21214 with
              | (uu____21223,tm,uu____21225,uu____21226) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____21186 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21259 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21259 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21277 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21305  ->
                match uu____21305 with
                | (u1,u2) ->
                    let uu____21312 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21313 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21312 uu____21313))
         in
      FStar_All.pipe_right uu____21277 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21340,[])) -> "{}"
      | uu____21365 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21388 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21388
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21391 =
              FStar_List.map
                (fun uu____21401  ->
                   match uu____21401 with
                   | (uu____21406,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21391 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21411 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21411 imps
  
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
                  let uu____21464 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21464
                  then
                    let uu____21465 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21466 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21465
                      (rel_to_string rel) uu____21466
                  else "TOP"  in
                let uu____21468 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21468 with
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
              let uu____21526 =
                let uu____21529 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21529
                 in
              FStar_Syntax_Syntax.new_bv uu____21526 t1  in
            let uu____21532 =
              let uu____21537 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21537
               in
            match uu____21532 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____21610 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21610
              then
                let uu____21611 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21611
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
          ((let uu____21633 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21633
            then
              let uu____21634 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21634
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21638 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21638
             then
               let uu____21639 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21639
             else ());
            (let f2 =
               let uu____21642 =
                 let uu____21643 = FStar_Syntax_Util.unmeta f1  in
                 uu____21643.FStar_Syntax_Syntax.n  in
               match uu____21642 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21647 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___358_21648 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___358_21648.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___358_21648.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___358_21648.FStar_TypeChecker_Env.implicits)
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
            let uu____21750 =
              let uu____21751 =
                let uu____21752 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21752;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21751  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21750
  
let with_guard_no_simp :
  'Auu____21767 .
    'Auu____21767 ->
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
            let uu____21790 =
              let uu____21791 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21791;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21790
  
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
          (let uu____21829 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21829
           then
             let uu____21830 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21831 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21830
               uu____21831
           else ());
          (let uu____21833 =
             let uu____21838 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____21838
              in
           match uu____21833 with
           | (prob,wl) ->
               let g =
                 let uu____21846 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21864  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21846  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21906 = try_teq true env t1 t2  in
        match uu____21906 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21910 = FStar_TypeChecker_Env.get_range env  in
              let uu____21911 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21910 uu____21911);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21918 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21918
              then
                let uu____21919 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21920 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21921 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21919
                  uu____21920 uu____21921
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
          let uu____21943 = FStar_TypeChecker_Env.get_range env  in
          let uu____21944 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21943 uu____21944
  
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
        (let uu____21969 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21969
         then
           let uu____21970 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21971 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21970 uu____21971
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21974 =
           let uu____21981 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____21981 "sub_comp"
            in
         match uu____21974 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____21992 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____22010  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____21992)))
  
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
      fun uu____22063  ->
        match uu____22063 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22106 =
                 let uu____22111 =
                   let uu____22112 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22113 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22112 uu____22113
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22111)  in
               let uu____22114 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22106 uu____22114)
               in
            let equiv1 v1 v' =
              let uu____22126 =
                let uu____22131 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22132 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22131, uu____22132)  in
              match uu____22126 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22151 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22181 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22181 with
                      | FStar_Syntax_Syntax.U_unif uu____22188 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22217  ->
                                    match uu____22217 with
                                    | (u,v') ->
                                        let uu____22226 = equiv1 v1 v'  in
                                        if uu____22226
                                        then
                                          let uu____22229 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22229 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22245 -> []))
               in
            let uu____22250 =
              let wl =
                let uu___359_22254 = empty_worklist env  in
                {
                  attempting = (uu___359_22254.attempting);
                  wl_deferred = (uu___359_22254.wl_deferred);
                  ctr = (uu___359_22254.ctr);
                  defer_ok = false;
                  smt_ok = (uu___359_22254.smt_ok);
                  tcenv = (uu___359_22254.tcenv);
                  wl_implicits = (uu___359_22254.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22272  ->
                      match uu____22272 with
                      | (lb,v1) ->
                          let uu____22279 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22279 with
                           | USolved wl1 -> ()
                           | uu____22281 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22291 =
              match uu____22291 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22300) -> true
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
                      uu____22323,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22325,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22336) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22343,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22351 -> false)
               in
            let uu____22356 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22371  ->
                      match uu____22371 with
                      | (u,v1) ->
                          let uu____22378 = check_ineq (u, v1)  in
                          if uu____22378
                          then true
                          else
                            ((let uu____22381 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22381
                              then
                                let uu____22382 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22383 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22382
                                  uu____22383
                              else ());
                             false)))
               in
            if uu____22356
            then ()
            else
              ((let uu____22387 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22387
                then
                  ((let uu____22389 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22389);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22399 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22399))
                else ());
               (let uu____22409 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22409))
  
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
        let fail1 uu____22476 =
          match uu____22476 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___360_22497 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___360_22497.attempting);
            wl_deferred = (uu___360_22497.wl_deferred);
            ctr = (uu___360_22497.ctr);
            defer_ok;
            smt_ok = (uu___360_22497.smt_ok);
            tcenv = (uu___360_22497.tcenv);
            wl_implicits = (uu___360_22497.wl_implicits)
          }  in
        (let uu____22499 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22499
         then
           let uu____22500 = FStar_Util.string_of_bool defer_ok  in
           let uu____22501 = wl_to_string wl  in
           let uu____22502 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22500 uu____22501 uu____22502
         else ());
        (let g1 =
           let uu____22513 = solve_and_commit env wl fail1  in
           match uu____22513 with
           | FStar_Pervasives_Native.Some
               (uu____22520::uu____22521,uu____22522) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___361_22547 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___361_22547.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___361_22547.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22556 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___362_22564 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___362_22564.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___362_22564.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___362_22564.FStar_TypeChecker_Env.implicits)
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
    let uu____22612 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22612 with
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
            let uu___363_22735 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___363_22735.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___363_22735.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___363_22735.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22736 =
            let uu____22737 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22737  in
          if uu____22736
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22745 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22746 =
                       let uu____22747 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22747
                        in
                     FStar_Errors.diag uu____22745 uu____22746)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22751 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22752 =
                        let uu____22753 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22753
                         in
                      FStar_Errors.diag uu____22751 uu____22752)
                   else ();
                   (let uu____22756 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22756 "discharge_guard'"
                      env vc1);
                   (let uu____22757 = check_trivial vc1  in
                    match uu____22757 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22764 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22765 =
                                let uu____22766 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22766
                                 in
                              FStar_Errors.diag uu____22764 uu____22765)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22771 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22772 =
                                let uu____22773 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22773
                                 in
                              FStar_Errors.diag uu____22771 uu____22772)
                           else ();
                           (let vcs =
                              let uu____22786 = FStar_Options.use_tactics ()
                                 in
                              if uu____22786
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22808  ->
                                     (let uu____22810 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22810);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22853  ->
                                              match uu____22853 with
                                              | (env1,goal,opts) ->
                                                  let uu____22869 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22869, opts)))))
                              else
                                (let uu____22871 =
                                   let uu____22880 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22880)  in
                                 [uu____22871])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22923  ->
                                    match uu____22923 with
                                    | (env1,goal,opts) ->
                                        let uu____22939 = check_trivial goal
                                           in
                                        (match uu____22939 with
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
                                                (let uu____22947 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22948 =
                                                   let uu____22949 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22950 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22949 uu____22950
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22947 uu____22948)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22953 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22954 =
                                                   let uu____22955 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22955
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22953 uu____22954)
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
      let uu____22969 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22969 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22976 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22976
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22987 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22987 with
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
            let uu____23020 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____23020 with
            | FStar_Pervasives_Native.Some uu____23023 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____23043 = acc  in
            match uu____23043 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____23095 = hd1  in
                     (match uu____23095 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23109 = unresolved ctx_u  in
                             if uu____23109
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___364_23121 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___364_23121.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___364_23121.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___364_23121.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___364_23121.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___364_23121.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___364_23121.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___364_23121.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___364_23121.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___364_23121.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___364_23121.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___364_23121.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___364_23121.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___364_23121.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___364_23121.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___364_23121.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___364_23121.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___364_23121.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___364_23121.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___364_23121.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___364_23121.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___364_23121.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___364_23121.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___364_23121.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___364_23121.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___364_23121.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___364_23121.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___364_23121.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___364_23121.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___364_23121.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___364_23121.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___364_23121.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___364_23121.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___364_23121.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___364_23121.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___364_23121.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___364_23121.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___364_23121.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___364_23121.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___365_23124 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___365_23124.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___365_23124.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___365_23124.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___365_23124.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___365_23124.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___365_23124.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___365_23124.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___365_23124.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___365_23124.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___365_23124.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___365_23124.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___365_23124.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___365_23124.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___365_23124.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___365_23124.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___365_23124.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___365_23124.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___365_23124.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___365_23124.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___365_23124.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___365_23124.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___365_23124.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___365_23124.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___365_23124.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___365_23124.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___365_23124.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___365_23124.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___365_23124.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___365_23124.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___365_23124.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___365_23124.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___365_23124.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___365_23124.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___365_23124.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___365_23124.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___365_23124.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___365_23124.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___365_23124.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____23127 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23127
                                   then
                                     let uu____23128 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____23129 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____23130 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____23131 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____23128 uu____23129 uu____23130
                                       reason uu____23131
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____23142 =
                                             let uu____23151 =
                                               let uu____23158 =
                                                 let uu____23159 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____23160 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____23161 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____23159 uu____23160
                                                   uu____23161
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____23158, r)
                                                in
                                             [uu____23151]  in
                                           FStar_Errors.add_errors
                                             uu____23142);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___368_23175 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___368_23175.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___368_23175.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___368_23175.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____23178 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____23188  ->
                                               let uu____23189 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____23190 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____23191 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____23189 uu____23190
                                                 reason uu____23191)) env2 g2
                                         true
                                        in
                                     match uu____23178 with
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
          let uu___369_23201 = g  in
          let uu____23202 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___369_23201.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___369_23201.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___369_23201.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23202
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
        let uu____23252 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23252 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23261 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23261
      | (reason,e,ctx_u,r)::uu____23266 ->
          let uu____23285 =
            let uu____23290 =
              let uu____23291 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23292 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23291 uu____23292 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23290)
             in
          FStar_Errors.raise_error uu____23285 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___370_23303 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___370_23303.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___370_23303.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___370_23303.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23318 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23318 with
      | FStar_Pervasives_Native.Some uu____23324 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23340 = try_teq false env t1 t2  in
        match uu____23340 with
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
        (let uu____23374 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23374
         then
           let uu____23375 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23376 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23375
             uu____23376
         else ());
        (let uu____23378 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23378 with
         | (prob,x,wl) ->
             let g =
               let uu____23397 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23415  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23397  in
             ((let uu____23443 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23443
               then
                 let uu____23444 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23445 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23446 =
                   let uu____23447 = FStar_Util.must g  in
                   guard_to_string env uu____23447  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23444 uu____23445 uu____23446
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
        let uu____23481 = check_subtyping env t1 t2  in
        match uu____23481 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23500 =
              let uu____23501 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23501 g  in
            FStar_Pervasives_Native.Some uu____23500
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23519 = check_subtyping env t1 t2  in
        match uu____23519 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23538 =
              let uu____23539 =
                let uu____23540 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23540]  in
              close_guard env uu____23539 g  in
            FStar_Pervasives_Native.Some uu____23538
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23569 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23569
         then
           let uu____23570 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23571 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23570
             uu____23571
         else ());
        (let uu____23573 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23573 with
         | (prob,x,wl) ->
             let g =
               let uu____23586 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23604  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23586  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23633 =
                      let uu____23634 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23634]  in
                    close_guard env uu____23633 g1  in
                  discharge_guard_nosmt env g2))
  