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
          let uu___148_160 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___148_160.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___148_160.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___148_160.FStar_TypeChecker_Env.implicits)
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
          let uu___149_309 = g  in
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
              (uu___149_309.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___149_309.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___149_309.FStar_TypeChecker_Env.implicits)
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
          let uu___150_392 = g  in
          let uu____393 =
            let uu____394 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____394  in
          {
            FStar_TypeChecker_Env.guard_f = uu____393;
            FStar_TypeChecker_Env.deferred =
              (uu___150_392.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___150_392.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___150_392.FStar_TypeChecker_Env.implicits)
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
            let uu___151_558 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___151_558.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___151_558.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___151_558.FStar_TypeChecker_Env.implicits)
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
            let uu___152_618 = g  in
            let uu____619 =
              let uu____620 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____620  in
            {
              FStar_TypeChecker_Env.guard_f = uu____619;
              FStar_TypeChecker_Env.deferred =
                (uu___152_618.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___152_618.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___152_618.FStar_TypeChecker_Env.implicits)
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
                   (let uu___153_1000 = wl  in
                    {
                      attempting = (uu___153_1000.attempting);
                      wl_deferred = (uu___153_1000.wl_deferred);
                      ctr = (uu___153_1000.ctr);
                      defer_ok = (uu___153_1000.defer_ok);
                      smt_ok = (uu___153_1000.smt_ok);
                      tcenv = (uu___153_1000.tcenv);
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
    match projectee with | Success _0 -> true | uu____1062 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1092 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____1117 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1123 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1129 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___115_1144  ->
    match uu___115_1144 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1150 = FStar_Syntax_Util.head_and_args t  in
    match uu____1150 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1209 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1210 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1224 =
                     let uu____1225 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1225  in
                   FStar_Util.format1 "@<%s>" uu____1224
                in
             let uu____1228 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1209 uu____1210 uu____1228
         | uu____1229 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___116_1239  ->
      match uu___116_1239 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1243 =
            let uu____1246 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1247 =
              let uu____1250 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1251 =
                let uu____1254 =
                  let uu____1257 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1257]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1254
                 in
              uu____1250 :: uu____1251  in
            uu____1246 :: uu____1247  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1243
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1261 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1262 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1263 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1261 uu____1262
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1263
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___117_1273  ->
      match uu___117_1273 with
      | UNIV (u,t) ->
          let x =
            let uu____1277 = FStar_Options.hide_uvar_nums ()  in
            if uu____1277
            then "?"
            else
              (let uu____1279 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1279 FStar_Util.string_of_int)
             in
          let uu____1280 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1280
      | TERM (u,t) ->
          let x =
            let uu____1284 = FStar_Options.hide_uvar_nums ()  in
            if uu____1284
            then "?"
            else
              (let uu____1286 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1286 FStar_Util.string_of_int)
             in
          let uu____1287 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1287
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1302 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1302 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1316 =
      let uu____1319 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1319
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1316 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1332 .
    (FStar_Syntax_Syntax.term,'Auu____1332) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1350 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1368  ->
              match uu____1368 with
              | (x,uu____1374) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1350 (FStar_String.concat " ")
  
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
        (let uu____1412 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1412
         then
           let uu____1413 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1413
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___118_1419  ->
    match uu___118_1419 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1424 .
    'Auu____1424 FStar_TypeChecker_Common.problem ->
      'Auu____1424 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___154_1436 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___154_1436.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___154_1436.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___154_1436.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___154_1436.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___154_1436.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___154_1436.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___154_1436.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1443 .
    'Auu____1443 FStar_TypeChecker_Common.problem ->
      'Auu____1443 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___119_1460  ->
    match uu___119_1460 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.TProb _0_17)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.CProb _0_18)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___120_1475  ->
    match uu___120_1475 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___155_1481 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___155_1481.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___155_1481.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___155_1481.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___155_1481.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___155_1481.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___155_1481.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___155_1481.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___155_1481.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___155_1481.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___156_1489 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___156_1489.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___156_1489.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___156_1489.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___156_1489.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___156_1489.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___156_1489.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___156_1489.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___156_1489.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___156_1489.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___121_1501  ->
      match uu___121_1501 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___122_1506  ->
    match uu___122_1506 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___123_1517  ->
    match uu___123_1517 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___124_1530  ->
    match uu___124_1530 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___125_1543  ->
    match uu___125_1543 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uu___126_1556  ->
    match uu___126_1556 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___127_1569  ->
    match uu___127_1569 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___128_1584  ->
    match uu___128_1584 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1603 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1603) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1631 =
          let uu____1632 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1632  in
        if uu____1631
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1666)::bs ->
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
        let uu____1733 =
          let uu____1734 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1734  in
        if uu____1733
        then ()
        else
          (let uu____1736 =
             let uu____1739 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1739
              in
           def_check_closed_in (p_loc prob) msg uu____1736 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1777 =
          let uu____1778 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1778  in
        if uu____1777
        then ()
        else
          (let uu____1780 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1780)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1795 =
        let uu____1796 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1796  in
      if uu____1795
      then ()
      else
        (let msgf m =
           let uu____1804 =
             let uu____1805 =
               let uu____1806 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1806 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1805  in
           Prims.strcat msg uu____1804  in
         (let uu____1808 = msgf "scope"  in
          let uu____1809 = p_scope prob  in
          def_scope_wf uu____1808 (p_loc prob) uu____1809);
         (let uu____1817 = msgf "guard"  in
          def_check_scoped uu____1817 prob (p_guard prob));
         (match p_element prob with
          | FStar_Pervasives_Native.Some t ->
              def_check_scoped (Prims.strcat "element." msg) prob t
          | FStar_Pervasives_Native.None  -> ());
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1824 = msgf "lhs"  in
                def_check_scoped uu____1824 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1825 = msgf "rhs"  in
                def_check_scoped uu____1825 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1830 = msgf "lhs"  in
                def_check_scoped_comp uu____1830 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1831 = msgf "rhs"  in
                def_check_scoped_comp uu____1831 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___157_1847 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___157_1847.wl_deferred);
          ctr = (uu___157_1847.ctr);
          defer_ok = (uu___157_1847.defer_ok);
          smt_ok;
          tcenv = (uu___157_1847.tcenv);
          wl_implicits = (uu___157_1847.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1854 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1854,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___158_1877 = empty_worklist env  in
      let uu____1878 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1878;
        wl_deferred = (uu___158_1877.wl_deferred);
        ctr = (uu___158_1877.ctr);
        defer_ok = (uu___158_1877.defer_ok);
        smt_ok = (uu___158_1877.smt_ok);
        tcenv = (uu___158_1877.tcenv);
        wl_implicits = (uu___158_1877.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___159_1898 = wl  in
        {
          attempting = (uu___159_1898.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___159_1898.ctr);
          defer_ok = (uu___159_1898.defer_ok);
          smt_ok = (uu___159_1898.smt_ok);
          tcenv = (uu___159_1898.tcenv);
          wl_implicits = (uu___159_1898.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___160_1920 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___160_1920.wl_deferred);
         ctr = (uu___160_1920.ctr);
         defer_ok = (uu___160_1920.defer_ok);
         smt_ok = (uu___160_1920.smt_ok);
         tcenv = (uu___160_1920.tcenv);
         wl_implicits = (uu___160_1920.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1931 .
    worklist ->
      'Auu____1931 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1960 = FStar_Syntax_Util.type_u ()  in
          match uu____1960 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1972 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1972 with
               | (uu____1983,tt,wl1) ->
                   let uu____1986 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1986, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___129_1991  ->
    match uu___129_1991 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.TProb _0_19) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.CProb _0_20) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2007 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2007 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____2019  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2117 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2117 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2117 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2117 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2183 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2183  in
                  let uu____2186 =
                    let uu____2193 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2193
                      guard_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2186 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2214 ->
                            let uu____2221 =
                              let uu____2226 =
                                FStar_List.map
                                  (fun uu____2239  ->
                                     match uu____2239 with
                                     | (x,i) ->
                                         let uu____2250 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2250, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2226  in
                            uu____2221 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let prob =
                        let uu____2256 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2256;
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
                      (prob, wl1)
  
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
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu____2320 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2320 with
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
                  (let uu____2399 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2399 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2435 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2435 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2435 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2435 FStar_TypeChecker_Common.problem,worklist)
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
                  let uu____2486 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2541 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2541]  in
                        let uu____2554 =
                          let uu____2557 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2557  in
                        let uu____2560 =
                          let uu____2563 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2563  in
                        (bs, uu____2554, uu____2560)
                     in
                  match uu____2486 with
                  | (bs,lg_ty,elt) ->
                      let uu____2603 =
                        let uu____2610 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___161_2618 = wl  in
                           {
                             attempting = (uu___161_2618.attempting);
                             wl_deferred = (uu___161_2618.wl_deferred);
                             ctr = (uu___161_2618.ctr);
                             defer_ok = (uu___161_2618.defer_ok);
                             smt_ok = (uu___161_2618.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___161_2618.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2610
                          lg_ty FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____2603 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2630 =
                                   let uu____2635 =
                                     let uu____2636 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2636]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2635
                                    in
                                 uu____2630 FStar_Pervasives_Native.None loc
                              in
                           let prob =
                             let uu____2660 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2660;
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
                let uu____2702 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2702;
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
  'Auu____2714 .
    worklist ->
      'Auu____2714 FStar_TypeChecker_Common.problem ->
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
        let uu____2764 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2764
        then
          let uu____2765 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2766 = prob_to_string env d  in
          let uu____2767 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2765 uu____2766 uu____2767 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2773 -> failwith "impossible"  in
           let uu____2774 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2786 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2787 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2786, uu____2787)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2791 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2792 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2791, uu____2792)
              in
           match uu____2774 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___130_2810  ->
            match uu___130_2810 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2822 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2826 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  def_check_closed_in t.FStar_Syntax_Syntax.pos "commit"
                    uu____2826 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___131_2851  ->
           match uu___131_2851 with
           | UNIV uu____2854 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2861 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2861
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
        (fun uu___132_2885  ->
           match uu___132_2885 with
           | UNIV (u',t) ->
               let uu____2890 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2890
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2894 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2905 =
        let uu____2906 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2906
         in
      FStar_Syntax_Subst.compress uu____2905
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2917 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2917
  
let norm_arg :
  'Auu____2924 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2924) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2924)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2947 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2947, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2988  ->
              match uu____2988 with
              | (x,imp) ->
                  let uu____2999 =
                    let uu___162_3000 = x  in
                    let uu____3001 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___162_3000.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___162_3000.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3001
                    }  in
                  (uu____2999, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3022 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3022
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3026 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3026
        | uu____3029 -> u2  in
      let uu____3030 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3030
  
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
                (let uu____3152 = norm_refinement env t12  in
                 match uu____3152 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3169;
                     FStar_Syntax_Syntax.vars = uu____3170;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3196 =
                       let uu____3197 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3198 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3197 uu____3198
                        in
                     failwith uu____3196)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3214 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3214
          | FStar_Syntax_Syntax.Tm_uinst uu____3215 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3252 =
                   let uu____3253 = FStar_Syntax_Subst.compress t1'  in
                   uu____3253.FStar_Syntax_Syntax.n  in
                 match uu____3252 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3270 -> aux true t1'
                 | uu____3277 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3292 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3323 =
                   let uu____3324 = FStar_Syntax_Subst.compress t1'  in
                   uu____3324.FStar_Syntax_Syntax.n  in
                 match uu____3323 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3341 -> aux true t1'
                 | uu____3348 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3363 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3408 =
                   let uu____3409 = FStar_Syntax_Subst.compress t1'  in
                   uu____3409.FStar_Syntax_Syntax.n  in
                 match uu____3408 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3426 -> aux true t1'
                 | uu____3433 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3448 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3463 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3478 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3493 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3508 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3535 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3566 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3587 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3616 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3643 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3680 ->
              let uu____3687 =
                let uu____3688 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3689 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3688 uu____3689
                 in
              failwith uu____3687
          | FStar_Syntax_Syntax.Tm_ascribed uu____3704 ->
              let uu____3731 =
                let uu____3732 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3733 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3732 uu____3733
                 in
              failwith uu____3731
          | FStar_Syntax_Syntax.Tm_delayed uu____3748 ->
              let uu____3773 =
                let uu____3774 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3775 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3774 uu____3775
                 in
              failwith uu____3773
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3790 =
                let uu____3791 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3792 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3791 uu____3792
                 in
              failwith uu____3790
           in
        let uu____3807 = whnf env t1  in aux false uu____3807
  
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
      let uu____3853 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3853 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3889 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3889, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3900 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3900 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3925 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3925 with
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
  fun uu____4008  ->
    match uu____4008 with
    | (t_base,refopt) ->
        let uu____4041 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4041 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4081 =
      let uu____4084 =
        let uu____4087 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4110  ->
                  match uu____4110 with | (uu____4117,uu____4118,x) -> x))
           in
        FStar_List.append wl.attempting uu____4087  in
      FStar_List.map (wl_prob_to_string wl) uu____4084  in
    FStar_All.pipe_right uu____4081 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____4132 .
    ('Auu____4132,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____4143  ->
    match uu____4143 with
    | (uu____4150,c,args) ->
        let uu____4153 = print_ctx_uvar c  in
        let uu____4154 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4153 uu____4154
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4160 = FStar_Syntax_Util.head_and_args t  in
    match uu____4160 with
    | (head1,_args) ->
        let uu____4197 =
          let uu____4198 = FStar_Syntax_Subst.compress head1  in
          uu____4198.FStar_Syntax_Syntax.n  in
        (match uu____4197 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4201 -> true
         | uu____4216 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4222 = FStar_Syntax_Util.head_and_args t  in
    match uu____4222 with
    | (head1,_args) ->
        let uu____4259 =
          let uu____4260 = FStar_Syntax_Subst.compress head1  in
          uu____4260.FStar_Syntax_Syntax.n  in
        (match uu____4259 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4264) -> u
         | uu____4285 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4308 = FStar_Syntax_Util.head_and_args t  in
      match uu____4308 with
      | (head1,args) ->
          let uu____4349 =
            let uu____4350 = FStar_Syntax_Subst.compress head1  in
            uu____4350.FStar_Syntax_Syntax.n  in
          (match uu____4349 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4358)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4401 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___133_4426  ->
                         match uu___133_4426 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4430 =
                               let uu____4431 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4431.FStar_Syntax_Syntax.n  in
                             (match uu____4430 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4435 -> false)
                         | uu____4436 -> true))
                  in
               (match uu____4401 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4458 =
                        FStar_List.collect
                          (fun uu___134_4464  ->
                             match uu___134_4464 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4468 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4468]
                             | uu____4469 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4458 FStar_List.rev  in
                    let uu____4478 =
                      let uu____4485 =
                        let uu____4492 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___135_4506  ->
                                  match uu___135_4506 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4510 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4510]
                                  | uu____4511 -> []))
                           in
                        FStar_All.pipe_right uu____4492 FStar_List.rev  in
                      let uu____4528 =
                        let uu____4531 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4531  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4485 uu____4528
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4478 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4560  ->
                                match uu____4560 with
                                | (x,i) ->
                                    let uu____4571 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4571, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4594  ->
                                match uu____4594 with
                                | (a,i) ->
                                    let uu____4605 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4605, i)) args_sol
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
           | uu____4621 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4641 =
          let uu____4654 =
            let uu____4655 = FStar_Syntax_Subst.compress k  in
            uu____4655.FStar_Syntax_Syntax.n  in
          match uu____4654 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4708 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4708)
              else
                (let uu____4722 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4722 with
                 | (ys',t1,uu____4745) ->
                     let uu____4750 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4750))
          | uu____4791 ->
              let uu____4792 =
                let uu____4803 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4803)  in
              ((ys, t), uu____4792)
           in
        match uu____4641 with
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
                 let uu____4852 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4852 c  in
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
               (let uu____4926 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4926
                then
                  let uu____4927 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4928 = print_ctx_uvar uv  in
                  let uu____4929 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4927 uu____4928 uu____4929
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4935 =
                   let uu____4936 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4936  in
                 let uu____4937 =
                   let uu____4940 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4940
                    in
                 def_check_closed_in (p_loc prob) uu____4935 uu____4937 phi2);
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
                  (let uu___163_5081 = wl1  in
                   {
                     attempting = (uu___163_5081.attempting);
                     wl_deferred = (uu___163_5081.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___163_5081.defer_ok);
                     smt_ok = (uu___163_5081.smt_ok);
                     tcenv = (uu___163_5081.tcenv);
                     wl_implicits = (uu___163_5081.wl_implicits)
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
        (let uu___164_5112 = wl  in
         {
           attempting = (uu___164_5112.attempting);
           wl_deferred = (uu___164_5112.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___164_5112.defer_ok);
           smt_ok = (uu___164_5112.smt_ok);
           tcenv = (uu___164_5112.tcenv);
           wl_implicits = (uu___164_5112.wl_implicits)
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
                 let uu____5200 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5200
              in
           (let uu____5206 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5206
            then
              let uu____5207 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5208 =
                let uu____5209 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5209 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5207 uu____5208
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
        let uu____5234 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5234 FStar_Util.set_elements  in
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
      let uu____5268 = occurs uk t  in
      match uu____5268 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5297 =
                 let uu____5298 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5299 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5298 uu____5299
                  in
               FStar_Pervasives_Native.Some uu____5297)
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
            let uu____5388 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5388 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5432 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5480  ->
             match uu____5480 with
             | (x,uu____5490) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5503 = FStar_List.last bs  in
      match uu____5503 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5521) ->
          let uu____5526 =
            FStar_Util.prefix_until
              (fun uu___136_5541  ->
                 match uu___136_5541 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5543 -> false) g
             in
          (match uu____5526 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5556,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5592 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5592 with
        | (pfx,uu____5602) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5614 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5614 with
             | (uu____5621,src',wl1) ->
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
                 | uu____5721 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5722 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5776  ->
                  fun uu____5777  ->
                    match (uu____5776, uu____5777) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5858 =
                          let uu____5859 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5859
                           in
                        if uu____5858
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5884 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5884
                           then
                             let uu____5897 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5897)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5722 with | (isect,uu____5934) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5963 'Auu____5964 .
    (FStar_Syntax_Syntax.bv,'Auu____5963) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5964) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6021  ->
              fun uu____6022  ->
                match (uu____6021, uu____6022) with
                | ((a,uu____6040),(b,uu____6042)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6057 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____6057) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6087  ->
           match uu____6087 with
           | (y,uu____6093) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6102 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____6102) FStar_Pervasives_Native.tuple2
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
                   let uu____6232 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6232
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6252 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6295 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6333 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6346 -> false
  
let string_of_option :
  'Auu____6353 .
    ('Auu____6353 -> Prims.string) ->
      'Auu____6353 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___137_6368  ->
      match uu___137_6368 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6374 = f x  in Prims.strcat "Some " uu____6374
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___138_6379  ->
    match uu___138_6379 with
    | MisMatch (d1,d2) ->
        let uu____6390 =
          let uu____6391 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6392 =
            let uu____6393 =
              let uu____6394 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6394 ")"  in
            Prims.strcat ") (" uu____6393  in
          Prims.strcat uu____6391 uu____6392  in
        Prims.strcat "MisMatch (" uu____6390
    | HeadMatch u ->
        let uu____6396 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6396
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___139_6401  ->
    match uu___139_6401 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6416 -> HeadMatch false
  
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
          let uu____6430 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6430 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6441 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6464 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6473 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6501 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6501
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6502 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6503 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6504 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6519 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6532 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6556) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6562,uu____6563) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6605) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6626;
             FStar_Syntax_Syntax.index = uu____6627;
             FStar_Syntax_Syntax.sort = t2;_},uu____6629)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6636 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6637 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6638 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6651 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6658 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6676 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6676
  
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
            let uu____6703 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6703
            then FullMatch
            else
              (let uu____6705 =
                 let uu____6714 =
                   let uu____6717 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6717  in
                 let uu____6718 =
                   let uu____6721 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6721  in
                 (uu____6714, uu____6718)  in
               MisMatch uu____6705)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6727),FStar_Syntax_Syntax.Tm_uinst (g,uu____6729)) ->
            let uu____6738 = head_matches env f g  in
            FStar_All.pipe_right uu____6738 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6741 = FStar_Const.eq_const c d  in
            if uu____6741
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6748),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6750)) ->
            let uu____6791 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6791
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6798),FStar_Syntax_Syntax.Tm_refine (y,uu____6800)) ->
            let uu____6809 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6809 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6811),uu____6812) ->
            let uu____6817 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6817 head_match
        | (uu____6818,FStar_Syntax_Syntax.Tm_refine (x,uu____6820)) ->
            let uu____6825 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6825 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6826,FStar_Syntax_Syntax.Tm_type
           uu____6827) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6828,FStar_Syntax_Syntax.Tm_arrow uu____6829) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6855),FStar_Syntax_Syntax.Tm_app (head',uu____6857))
            ->
            let uu____6898 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6898 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6900),uu____6901) ->
            let uu____6922 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6922 head_match
        | (uu____6923,FStar_Syntax_Syntax.Tm_app (head1,uu____6925)) ->
            let uu____6946 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6946 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6947,FStar_Syntax_Syntax.Tm_let
           uu____6948) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6973,FStar_Syntax_Syntax.Tm_match uu____6974) ->
            HeadMatch true
        | uu____7019 ->
            let uu____7024 =
              let uu____7033 = delta_depth_of_term env t11  in
              let uu____7036 = delta_depth_of_term env t21  in
              (uu____7033, uu____7036)  in
            MisMatch uu____7024
  
let head_matches_delta :
  'Auu____7053 .
    FStar_TypeChecker_Env.env ->
      'Auu____7053 ->
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
            (let uu____7102 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7102
             then
               let uu____7103 = FStar_Syntax_Print.term_to_string t  in
               let uu____7104 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7103 uu____7104
             else ());
            (let uu____7106 =
               let uu____7107 = FStar_Syntax_Util.un_uinst head1  in
               uu____7107.FStar_Syntax_Syntax.n  in
             match uu____7106 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7113 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7113 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7127 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7127
                        then
                          let uu____7128 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7128
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7130 ->
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
                      ((let uu____7141 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7141
                        then
                          let uu____7142 =
                            FStar_Syntax_Print.term_to_string t  in
                          let uu____7143 =
                            FStar_Syntax_Print.term_to_string t'  in
                          FStar_Util.print2 "Inlined %s to %s\n" uu____7142
                            uu____7143
                        else ());
                       FStar_Pervasives_Native.Some t'))
             | uu____7145 -> FStar_Pervasives_Native.None)
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
            (let uu____7283 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7283
             then
               let uu____7284 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7285 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7286 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7284
                 uu____7285 uu____7286
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7310 =
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
               match uu____7310 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7355 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7355 with
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
                  uu____7387),uu____7388)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7406 =
                      let uu____7415 = maybe_inline t11  in
                      let uu____7418 = maybe_inline t21  in
                      (uu____7415, uu____7418)  in
                    match uu____7406 with
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
                 (uu____7455,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7456))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7474 =
                      let uu____7483 = maybe_inline t11  in
                      let uu____7486 = maybe_inline t21  in
                      (uu____7483, uu____7486)  in
                    match uu____7474 with
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
             | MisMatch uu____7535 -> fail1 n_delta r t11 t21
             | uu____7544 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7557 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7557
           then
             let uu____7558 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7559 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7560 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7567 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7585 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7585
                    (fun uu____7619  ->
                       match uu____7619 with
                       | (t11,t21) ->
                           let uu____7626 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7627 =
                             let uu____7628 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7628  in
                           Prims.strcat uu____7626 uu____7627))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7558 uu____7559 uu____7560 uu____7567
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7640 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7640 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___140_7653  ->
    match uu___140_7653 with
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
      let uu___165_7690 = p  in
      let uu____7693 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7694 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___165_7690.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7693;
        FStar_TypeChecker_Common.relation =
          (uu___165_7690.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7694;
        FStar_TypeChecker_Common.element =
          (uu___165_7690.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___165_7690.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___165_7690.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___165_7690.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___165_7690.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___165_7690.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7708 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7708
            (fun _0_21  -> FStar_TypeChecker_Common.TProb _0_21)
      | FStar_TypeChecker_Common.CProb uu____7713 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7735 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7735 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7743 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7743 with
           | (lh,lhs_args) ->
               let uu____7784 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7784 with
                | (rh,rhs_args) ->
                    let uu____7825 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7838,FStar_Syntax_Syntax.Tm_uvar uu____7839)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7920 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7943,uu____7944)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7961,FStar_Syntax_Syntax.Tm_uvar uu____7962)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7979,FStar_Syntax_Syntax.Tm_arrow uu____7980)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8010 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8010.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8010.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8010.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8010.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8010.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8010.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8010.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8010.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8010.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8013,FStar_Syntax_Syntax.Tm_type uu____8014)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8032 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8032.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8032.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8032.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8032.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8032.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8032.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8032.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8032.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8032.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8035,FStar_Syntax_Syntax.Tm_uvar uu____8036)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___166_8054 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___166_8054.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___166_8054.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___166_8054.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___166_8054.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___166_8054.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___166_8054.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___166_8054.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___166_8054.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___166_8054.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8057,FStar_Syntax_Syntax.Tm_uvar uu____8058)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8075,uu____8076)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8093,FStar_Syntax_Syntax.Tm_uvar uu____8094)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8111,uu____8112) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7825 with
                     | (rank,tp1) ->
                         let uu____8125 =
                           FStar_All.pipe_right
                             (let uu___167_8129 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___167_8129.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___167_8129.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___167_8129.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___167_8129.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___167_8129.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___167_8129.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___167_8129.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___167_8129.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___167_8129.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_22  ->
                                FStar_TypeChecker_Common.TProb _0_22)
                            in
                         (rank, uu____8125))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8135 =
            FStar_All.pipe_right
              (let uu___168_8139 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___168_8139.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___168_8139.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___168_8139.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___168_8139.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___168_8139.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___168_8139.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___168_8139.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___168_8139.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___168_8139.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_23  -> FStar_TypeChecker_Common.CProb _0_23)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8135)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8200 probs =
      match uu____8200 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8281 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8302 = rank wl.tcenv hd1  in
               (match uu____8302 with
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
                      (let uu____8361 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8365 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8365)
                          in
                       if uu____8361
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
          let uu____8433 = FStar_Syntax_Util.head_and_args t  in
          match uu____8433 with
          | (hd1,uu____8449) ->
              let uu____8470 =
                let uu____8471 = FStar_Syntax_Subst.compress hd1  in
                uu____8471.FStar_Syntax_Syntax.n  in
              (match uu____8470 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8475) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8509  ->
                           match uu____8509 with
                           | (y,uu____8515) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8529  ->
                                       match uu____8529 with
                                       | (x,uu____8535) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8536 -> false)
           in
        let uu____8537 = rank tcenv p  in
        match uu____8537 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8544 -> true
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
    match projectee with | UDeferred _0 -> true | uu____8571 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8585 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8599 -> false
  
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
                        let uu____8651 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8651 with
                        | (k,uu____8657) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8667 -> false)))
            | uu____8668 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8720 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8726 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8726 = (Prims.parse_int "0")))
                           in
                        if uu____8720 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8742 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8748 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8748 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8742)
               in
            let uu____8749 = filter1 u12  in
            let uu____8752 = filter1 u22  in (uu____8749, uu____8752)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8781 = filter_out_common_univs us1 us2  in
                (match uu____8781 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8840 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8840 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8843 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8853 =
                          let uu____8854 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8855 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8854
                            uu____8855
                           in
                        UFailed uu____8853))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8879 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8879 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8905 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8905 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8908 ->
                let uu____8913 =
                  let uu____8914 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8915 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8914
                    uu____8915 msg
                   in
                UFailed uu____8913
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8916,uu____8917) ->
              let uu____8918 =
                let uu____8919 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8920 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8919 uu____8920
                 in
              failwith uu____8918
          | (FStar_Syntax_Syntax.U_unknown ,uu____8921) ->
              let uu____8922 =
                let uu____8923 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8924 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8923 uu____8924
                 in
              failwith uu____8922
          | (uu____8925,FStar_Syntax_Syntax.U_bvar uu____8926) ->
              let uu____8927 =
                let uu____8928 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8929 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8928 uu____8929
                 in
              failwith uu____8927
          | (uu____8930,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8931 =
                let uu____8932 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8933 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8932 uu____8933
                 in
              failwith uu____8931
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8957 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8957
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8971 = occurs_univ v1 u3  in
              if uu____8971
              then
                let uu____8972 =
                  let uu____8973 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8974 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8973 uu____8974
                   in
                try_umax_components u11 u21 uu____8972
              else
                (let uu____8976 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8976)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8988 = occurs_univ v1 u3  in
              if uu____8988
              then
                let uu____8989 =
                  let uu____8990 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8991 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8990 uu____8991
                   in
                try_umax_components u11 u21 uu____8989
              else
                (let uu____8993 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8993)
          | (FStar_Syntax_Syntax.U_max uu____8994,uu____8995) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9001 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9001
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9003,FStar_Syntax_Syntax.U_max uu____9004) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____9010 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____9010
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9012,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9013,FStar_Syntax_Syntax.U_name
             uu____9014) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____9015) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____9016) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9017,FStar_Syntax_Syntax.U_succ
             uu____9018) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9019,FStar_Syntax_Syntax.U_zero
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
      let uu____9119 = bc1  in
      match uu____9119 with
      | (bs1,mk_cod1) ->
          let uu____9163 = bc2  in
          (match uu____9163 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9274 = aux xs ys  in
                     (match uu____9274 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9357 =
                       let uu____9364 = mk_cod1 xs  in ([], uu____9364)  in
                     let uu____9367 =
                       let uu____9374 = mk_cod2 ys  in ([], uu____9374)  in
                     (uu____9357, uu____9367)
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
                  let uu____9444 =
                    let uu____9445 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9445 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9444
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9450 = has_type_guard t1 t2  in (uu____9450, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9451 = has_type_guard t2 t1  in (uu____9451, wl)
  
let is_flex_pat :
  'Auu____9460 'Auu____9461 'Auu____9462 .
    ('Auu____9460,'Auu____9461,'Auu____9462 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___141_9475  ->
    match uu___141_9475 with
    | (uu____9484,uu____9485,[]) -> true
    | uu____9488 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9519 = f  in
      match uu____9519 with
      | (uu____9526,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9527;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9528;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9531;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9532;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9533;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9585  ->
                 match uu____9585 with
                 | (y,uu____9591) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9713 =
                  let uu____9726 =
                    let uu____9729 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9729  in
                  ((FStar_List.rev pat_binders), uu____9726)  in
                FStar_Pervasives_Native.Some uu____9713
            | (uu____9756,[]) ->
                let uu____9779 =
                  let uu____9792 =
                    let uu____9795 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9795  in
                  ((FStar_List.rev pat_binders), uu____9792)  in
                FStar_Pervasives_Native.Some uu____9779
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9860 =
                  let uu____9861 = FStar_Syntax_Subst.compress a  in
                  uu____9861.FStar_Syntax_Syntax.n  in
                (match uu____9860 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9879 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9879
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___169_9900 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___169_9900.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___169_9900.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9904 =
                            let uu____9905 =
                              let uu____9912 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9912)  in
                            FStar_Syntax_Syntax.NT uu____9905  in
                          [uu____9904]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___170_9924 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___170_9924.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___170_9924.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9925 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9953 =
                  let uu____9966 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9966  in
                (match uu____9953 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10029 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10056 ->
               let uu____10057 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10057 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10333 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10333
       then
         let uu____10334 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10334
       else ());
      (let uu____10336 = next_prob probs  in
       match uu____10336 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___171_10363 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___171_10363.wl_deferred);
               ctr = (uu___171_10363.ctr);
               defer_ok = (uu___171_10363.defer_ok);
               smt_ok = (uu___171_10363.smt_ok);
               tcenv = (uu___171_10363.tcenv);
               wl_implicits = (uu___171_10363.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10371 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10371
                 then
                   let uu____10372 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10372
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
                           (let uu___172_10377 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___172_10377.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___172_10377.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___172_10377.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___172_10377.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___172_10377.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___172_10377.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___172_10377.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___172_10377.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___172_10377.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10399 ->
                let uu____10408 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10467  ->
                          match uu____10467 with
                          | (c,uu____10475,uu____10476) -> c < probs.ctr))
                   in
                (match uu____10408 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10517 =
                            let uu____10522 =
                              FStar_List.map
                                (fun uu____10537  ->
                                   match uu____10537 with
                                   | (uu____10548,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10522, (probs.wl_implicits))  in
                          Success uu____10517
                      | uu____10551 ->
                          let uu____10560 =
                            let uu___173_10561 = probs  in
                            let uu____10562 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10581  ->
                                      match uu____10581 with
                                      | (uu____10588,uu____10589,y) -> y))
                               in
                            {
                              attempting = uu____10562;
                              wl_deferred = rest;
                              ctr = (uu___173_10561.ctr);
                              defer_ok = (uu___173_10561.defer_ok);
                              smt_ok = (uu___173_10561.smt_ok);
                              tcenv = (uu___173_10561.tcenv);
                              wl_implicits = (uu___173_10561.wl_implicits)
                            }  in
                          solve env uu____10560))))

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
            let uu____10596 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10596 with
            | USolved wl1 ->
                let uu____10598 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10598
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
                  let uu____10650 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10650 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10653 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10665;
                  FStar_Syntax_Syntax.vars = uu____10666;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10669;
                  FStar_Syntax_Syntax.vars = uu____10670;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10682,uu____10683) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10690,FStar_Syntax_Syntax.Tm_uinst uu____10691) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10698 -> USolved wl

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
            ((let uu____10708 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10708
              then
                let uu____10709 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10709 msg
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
               let uu____10795 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10795 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10848 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10848
                then
                  let uu____10849 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10850 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10849 uu____10850
                else ());
               (let uu____10852 = head_matches_delta env1 () t1 t2  in
                match uu____10852 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____10897 = eq_prob t1 t2 wl2  in
                         (match uu____10897 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____10918 ->
                         let uu____10927 = eq_prob t1 t2 wl2  in
                         (match uu____10927 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____10974 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____10989 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____10990 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____10989, uu____10990)
                           | FStar_Pervasives_Native.None  ->
                               let uu____10995 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____10996 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____10995, uu____10996)
                            in
                         (match uu____10974 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11027 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11027 with
                                | (t1_hd,t1_args) ->
                                    let uu____11066 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11066 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11120 =
                                              let uu____11127 =
                                                let uu____11136 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11136 :: t1_args  in
                                              let uu____11149 =
                                                let uu____11156 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11156 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11197  ->
                                                   fun uu____11198  ->
                                                     fun uu____11199  ->
                                                       match (uu____11197,
                                                               uu____11198,
                                                               uu____11199)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11241),
                                                          (a2,uu____11243))
                                                           ->
                                                           let uu____11268 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11268
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11127
                                                uu____11149
                                               in
                                            match uu____11120 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___174_11294 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___174_11294.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    tcenv =
                                                      (uu___174_11294.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11310 =
                                                  solve env1 wl'  in
                                                (match uu____11310 with
                                                 | Success (uu____11313,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___175_11317
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___175_11317.attempting);
                                                            wl_deferred =
                                                              (uu___175_11317.wl_deferred);
                                                            ctr =
                                                              (uu___175_11317.ctr);
                                                            defer_ok =
                                                              (uu___175_11317.defer_ok);
                                                            smt_ok =
                                                              (uu___175_11317.smt_ok);
                                                            tcenv =
                                                              (uu___175_11317.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11326 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11358 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11358 with
                                | (t1_base,p1_opt) ->
                                    let uu____11405 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11405 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11515 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11515
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
                                               let uu____11563 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11563
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
                                               let uu____11593 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11593
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
                                               let uu____11623 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11623
                                           | uu____11626 -> t_base  in
                                         let uu____11643 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11643 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11657 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11657, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11664 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11664 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11711 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11711 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11758 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11758
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
                              let uu____11782 = combine t11 t21 wl2  in
                              (match uu____11782 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11815 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11815
                                     then
                                       let uu____11816 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11816
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11855 ts1 =
               match uu____11855 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____11918 = pairwise out t wl2  in
                        (match uu____11918 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____11954 =
               let uu____11965 = FStar_List.hd ts  in (uu____11965, [], wl1)
                in
             let uu____11974 = FStar_List.tl ts  in
             aux uu____11954 uu____11974  in
           let uu____11981 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____11981 with
           | (this_flex,this_rigid) ->
               let uu____11993 =
                 let uu____11994 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____11994.FStar_Syntax_Syntax.n  in
               (match uu____11993 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12015 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12015
                    then
                      let uu____12016 = destruct_flex_t this_flex wl  in
                      (match uu____12016 with
                       | (flex,wl1) ->
                           let uu____12023 = quasi_pattern env flex  in
                           (match uu____12023 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12041 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12041
                                  then
                                    let uu____12042 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12042
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12045 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___176_12048 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___176_12048.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___176_12048.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___176_12048.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___176_12048.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___176_12048.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___176_12048.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___176_12048.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___176_12048.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___176_12048.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12045)
                | uu____12049 ->
                    ((let uu____12051 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12051
                      then
                        let uu____12052 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12052
                      else ());
                     (let uu____12054 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12054 with
                      | (u,_args) ->
                          let uu____12091 =
                            let uu____12092 = FStar_Syntax_Subst.compress u
                               in
                            uu____12092.FStar_Syntax_Syntax.n  in
                          (match uu____12091 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12123 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12123 with
                                 | (u',uu____12139) ->
                                     let uu____12160 =
                                       let uu____12161 = whnf env u'  in
                                       uu____12161.FStar_Syntax_Syntax.n  in
                                     (match uu____12160 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12186 -> false)
                                  in
                               let uu____12187 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___142_12210  ->
                                         match uu___142_12210 with
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
                                              | uu____12219 -> false)
                                         | uu____12222 -> false))
                                  in
                               (match uu____12187 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12236 = whnf env this_rigid
                                         in
                                      let uu____12237 =
                                        FStar_List.collect
                                          (fun uu___143_12243  ->
                                             match uu___143_12243 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12249 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12249]
                                             | uu____12251 -> [])
                                          bounds_probs
                                         in
                                      uu____12236 :: uu____12237  in
                                    let uu____12252 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12252 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12283 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12298 =
                                               let uu____12299 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12299.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12298 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12311 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12311)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12320 -> bound  in
                                           let uu____12321 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12321)  in
                                         (match uu____12283 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12350 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12350
                                                then
                                                  let wl'1 =
                                                    let uu___177_12352 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___177_12352.wl_deferred);
                                                      ctr =
                                                        (uu___177_12352.ctr);
                                                      defer_ok =
                                                        (uu___177_12352.defer_ok);
                                                      smt_ok =
                                                        (uu___177_12352.smt_ok);
                                                      tcenv =
                                                        (uu___177_12352.tcenv);
                                                      wl_implicits =
                                                        (uu___177_12352.wl_implicits)
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
                                                    (let uu___178_12358 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___178_12358.wl_deferred);
                                                       ctr =
                                                         (uu___178_12358.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___178_12358.smt_ok);
                                                       tcenv =
                                                         (uu___178_12358.tcenv);
                                                       wl_implicits =
                                                         (uu___178_12358.wl_implicits)
                                                     })
                                                   in
                                                match uu____12356 with
                                                | Success uu____12359 ->
                                                    let wl2 =
                                                      let uu___179_12365 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___179_12365.wl_deferred);
                                                        ctr =
                                                          (uu___179_12365.ctr);
                                                        defer_ok =
                                                          (uu___179_12365.defer_ok);
                                                        smt_ok =
                                                          (uu___179_12365.smt_ok);
                                                        tcenv =
                                                          (uu___179_12365.tcenv);
                                                        wl_implicits =
                                                          (uu___179_12365.wl_implicits)
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
                                                                 let uu____12479
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12479)))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          let uu____12503 =
                                                            new_problem wl1
                                                              env t_base
                                                              FStar_TypeChecker_Common.EQ
                                                              this_flex
                                                              FStar_Pervasives_Native.None
                                                              tp.FStar_TypeChecker_Common.loc
                                                              "widened subtyping"
                                                             in
                                                          (match uu____12503
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
                                                                   let uu____12521
                                                                    =
                                                                    let uu____12526
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12526
                                                                     in
                                                                   solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12521
                                                                    [] wl2
                                                                    in
                                                                 let uu____12531
                                                                   =
                                                                   attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3
                                                                    in
                                                                 solve env
                                                                   uu____12531)))
                                                      | uu____12532 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12547 when flip ->
                               let uu____12548 =
                                 let uu____12549 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12550 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12549 uu____12550
                                  in
                               failwith uu____12548
                           | uu____12551 ->
                               let uu____12552 =
                                 let uu____12553 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12554 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12553 uu____12554
                                  in
                               failwith uu____12552)))))

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
                      (fun uu____12582  ->
                         match uu____12582 with
                         | (x,i) ->
                             let uu____12593 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12593, i)) bs_lhs
                     in
                  let uu____12594 = lhs  in
                  match uu____12594 with
                  | (uu____12595,u_lhs,uu____12597) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12710 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12720 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12720, univ)
                             in
                          match uu____12710 with
                          | (k,univ) ->
                              let uu____12733 =
                                let uu____12740 =
                                  let uu____12743 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12743
                                   in
                                copy_uvar u_lhs uu____12740 wl2  in
                              (match uu____12733 with
                               | (uu____12756,u,wl3) ->
                                   let uu____12759 =
                                     let uu____12762 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12762
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12759, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12798 =
                              let uu____12811 =
                                let uu____12820 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12820 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12866  ->
                                   fun uu____12867  ->
                                     match (uu____12866, uu____12867) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12958 =
                                           let uu____12965 =
                                             let uu____12968 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12968
                                              in
                                           copy_uvar u_lhs uu____12965 wl2
                                            in
                                         (match uu____12958 with
                                          | (uu____12991,t_a,wl3) ->
                                              let uu____12994 =
                                                let uu____13001 =
                                                  let uu____13004 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____13004
                                                   in
                                                copy_uvar u_lhs uu____13001
                                                  wl3
                                                 in
                                              (match uu____12994 with
                                               | (uu____13019,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12811
                                ([], wl1)
                               in
                            (match uu____12798 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___180_13080 = ct  in
                                   let uu____13081 =
                                     let uu____13084 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13084
                                      in
                                   let uu____13099 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___180_13080.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___180_13080.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13081;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13099;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___180_13080.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___181_13117 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___181_13117.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___181_13117.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13120 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13120 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13174 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13174 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13191 =
                                          let uu____13196 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13196)  in
                                        TERM uu____13191  in
                                      let uu____13197 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13197 with
                                       | (sub_prob,wl3) ->
                                           let uu____13208 =
                                             let uu____13209 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13209
                                              in
                                           solve env uu____13208))
                             | (x,imp)::formals2 ->
                                 let uu____13223 =
                                   let uu____13230 =
                                     let uu____13233 =
                                       let uu____13236 =
                                         let uu____13237 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____13237
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____13236
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____13233
                                      in
                                   copy_uvar u_lhs uu____13230 wl1  in
                                 (match uu____13223 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____13261 =
                                          let uu____13264 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13264
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13261 t_y
                                         in
                                      let uu____13265 =
                                        let uu____13268 =
                                          let uu____13271 =
                                            let uu____13272 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13272, imp)  in
                                          [uu____13271]  in
                                        FStar_List.append bs_terms
                                          uu____13268
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13265 formals2 wl2)
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
              (let uu____13314 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13314
               then
                 let uu____13315 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13316 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13315 (rel_to_string (p_rel orig)) uu____13316
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13421 = rhs wl1 scope env1 subst1  in
                     (match uu____13421 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13441 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13441
                            then
                              let uu____13442 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13442
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___182_13496 = hd1  in
                       let uu____13497 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___182_13496.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___182_13496.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13497
                       }  in
                     let hd21 =
                       let uu___183_13501 = hd2  in
                       let uu____13502 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___183_13501.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___183_13501.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13502
                       }  in
                     let uu____13505 =
                       let uu____13510 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13510
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13505 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13529 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13529
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13533 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13533 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13588 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13588
                                  in
                               ((let uu____13600 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13600
                                 then
                                   let uu____13601 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13602 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13601
                                     uu____13602
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13629 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13658 = aux wl [] env [] bs1 bs2  in
               match uu____13658 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13705 = attempt sub_probs wl2  in
                   solve env uu____13705)

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13710 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13710 wl)

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
              let uu____13724 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13724 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13754 = lhs1  in
              match uu____13754 with
              | (uu____13757,ctx_u,uu____13759) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13765 ->
                        let uu____13766 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13766 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13813 = quasi_pattern env1 lhs1  in
              match uu____13813 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13843) ->
                  let uu____13848 = lhs1  in
                  (match uu____13848 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13862 = occurs_check ctx_u rhs1  in
                       (match uu____13862 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13904 =
                                let uu____13911 =
                                  let uu____13912 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13912
                                   in
                                FStar_Util.Inl uu____13911  in
                              (uu____13904, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13932 =
                                 let uu____13933 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13933  in
                               if uu____13932
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13953 =
                                    let uu____13960 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13960  in
                                  let uu____13965 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13953, uu____13965)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____14027  ->
                     match uu____14027 with
                     | (x,i) ->
                         let uu____14038 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____14038, i)) bs_lhs
                 in
              let uu____14039 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14039 with
              | (rhs_hd,args) ->
                  let uu____14076 = FStar_Util.prefix args  in
                  (match uu____14076 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14134 = lhs1  in
                       (match uu____14134 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14138 =
                              let uu____14149 =
                                let uu____14156 =
                                  let uu____14159 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14159
                                   in
                                copy_uvar u_lhs uu____14156 wl1  in
                              match uu____14149 with
                              | (uu____14180,t_last_arg,wl2) ->
                                  let uu____14183 =
                                    let uu____14190 =
                                      let uu____14193 =
                                        let uu____14200 =
                                          let uu____14207 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____14207]  in
                                        FStar_List.append bs_lhs uu____14200
                                         in
                                      let uu____14224 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____14193
                                        uu____14224
                                       in
                                    copy_uvar u_lhs uu____14190 wl2  in
                                  (match uu____14183 with
                                   | (uu____14237,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14243 =
                                         let uu____14250 =
                                           let uu____14253 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____14253
                                            in
                                         copy_uvar u_lhs uu____14250 wl3  in
                                       (match uu____14243 with
                                        | (uu____14266,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14138 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14290 =
                                     let uu____14291 =
                                       let uu____14296 =
                                         let uu____14297 =
                                           let uu____14300 =
                                             let uu____14305 =
                                               let uu____14306 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14306]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14305
                                              in
                                           uu____14300
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14297
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14296)  in
                                     TERM uu____14291  in
                                   [uu____14290]  in
                                 let uu____14327 =
                                   let uu____14334 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14334 with
                                   | (p1,wl3) ->
                                       let uu____14351 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14351 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14327 with
                                  | (sub_probs,wl3) ->
                                      let uu____14378 =
                                        let uu____14379 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14379  in
                                      solve env1 uu____14378))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14412 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14412 with
                | (uu____14427,args) ->
                    (match args with | [] -> false | uu____14455 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14470 =
                  let uu____14471 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14471.FStar_Syntax_Syntax.n  in
                match uu____14470 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14474 -> true
                | uu____14487 -> false  in
              let uu____14488 = quasi_pattern env1 lhs1  in
              match uu____14488 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14499 =
                    let uu____14500 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14500
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14499
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14507 = is_app rhs1  in
                  if uu____14507
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14509 = is_arrow rhs1  in
                     if uu____14509
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14511 =
                          let uu____14512 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14512
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14511))
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
                let uu____14515 = lhs  in
                (match uu____14515 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14519 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14519 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14534 =
                              let uu____14537 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14537
                               in
                            FStar_All.pipe_right uu____14534
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14552 = occurs_check ctx_uv rhs1  in
                          (match uu____14552 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14574 =
                                   let uu____14575 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14575
                                    in
                                 giveup_or_defer env orig wl uu____14574
                               else
                                 (let uu____14577 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14577
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14582 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14582
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14584 =
                                         let uu____14585 =
                                           names_to_string1 fvs2  in
                                         let uu____14586 =
                                           names_to_string1 fvs1  in
                                         let uu____14587 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14585 uu____14586
                                           uu____14587
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14584)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14593 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14597 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14597 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14620 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14620
                             | (FStar_Util.Inl msg,uu____14622) ->
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
                  (let uu____14651 =
                     let uu____14668 = quasi_pattern env lhs  in
                     let uu____14675 = quasi_pattern env rhs  in
                     (uu____14668, uu____14675)  in
                   match uu____14651 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14718 = lhs  in
                       (match uu____14718 with
                        | ({ FStar_Syntax_Syntax.n = uu____14719;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14721;_},u_lhs,uu____14723)
                            ->
                            let uu____14726 = rhs  in
                            (match uu____14726 with
                             | (uu____14727,u_rhs,uu____14729) ->
                                 let uu____14730 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14730
                                 then
                                   let uu____14731 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14731
                                 else
                                   (let uu____14733 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14733 with
                                    | (sub_prob,wl1) ->
                                        let uu____14744 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14744 with
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
                                             let uu____14772 =
                                               let uu____14779 =
                                                 let uu____14782 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14782
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
                                                 uu____14779
                                                 FStar_Syntax_Syntax.Strict
                                                in
                                             (match uu____14772 with
                                              | (uu____14785,w,wl2) ->
                                                  let w_app =
                                                    let uu____14791 =
                                                      let uu____14796 =
                                                        FStar_List.map
                                                          (fun uu____14805 
                                                             ->
                                                             match uu____14805
                                                             with
                                                             | (z,uu____14811)
                                                                 ->
                                                                 let uu____14812
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14812)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14796
                                                       in
                                                    uu____14791
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14816 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14816
                                                    then
                                                      let uu____14817 =
                                                        let uu____14820 =
                                                          flex_t_to_string
                                                            lhs
                                                           in
                                                        let uu____14821 =
                                                          let uu____14824 =
                                                            flex_t_to_string
                                                              rhs
                                                             in
                                                          let uu____14825 =
                                                            let uu____14828 =
                                                              term_to_string
                                                                w
                                                               in
                                                            let uu____14829 =
                                                              let uu____14832
                                                                =
                                                                FStar_Syntax_Print.binders_to_string
                                                                  ", "
                                                                  (FStar_List.append
                                                                    ctx_l
                                                                    binders_lhs)
                                                                 in
                                                              let uu____14837
                                                                =
                                                                let uu____14840
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    (
                                                                    FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                   in
                                                                let uu____14845
                                                                  =
                                                                  let uu____14848
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ", " zs
                                                                     in
                                                                  [uu____14848]
                                                                   in
                                                                uu____14840
                                                                  ::
                                                                  uu____14845
                                                                 in
                                                              uu____14832 ::
                                                                uu____14837
                                                               in
                                                            uu____14828 ::
                                                              uu____14829
                                                             in
                                                          uu____14824 ::
                                                            uu____14825
                                                           in
                                                        uu____14820 ::
                                                          uu____14821
                                                         in
                                                      FStar_Util.print
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                        uu____14817
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14854 =
                                                          let uu____14859 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14859)
                                                           in
                                                        TERM uu____14854  in
                                                      let uu____14860 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14860
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14865 =
                                                             let uu____14870
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
                                                               uu____14870)
                                                              in
                                                           TERM uu____14865
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14871 =
                                                      let uu____14872 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14872
                                                       in
                                                    solve env uu____14871)))))))
                   | uu____14873 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif orig wl1 t1 t2 =
           (let uu____14937 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14937
            then
              let uu____14938 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14939 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14940 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14941 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____14938 uu____14939 uu____14940 uu____14941
            else ());
           (let uu____14945 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____14945
            then
              let uu____14946 = FStar_Syntax_Print.term_to_string t1  in
              let uu____14947 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____14948 = FStar_Syntax_Print.term_to_string t2  in
              let uu____14949 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print4
                "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                uu____14946 uu____14947 uu____14948 uu____14949
            else ());
           (let uu____14951 = FStar_Syntax_Util.head_and_args t1  in
            match uu____14951 with
            | (head1,args1) ->
                let uu____14988 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____14988 with
                 | (head2,args2) ->
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15042 =
                         let uu____15043 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15044 = args_to_string args1  in
                         let uu____15045 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15046 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15043 uu____15044 uu____15045 uu____15046
                          in
                       giveup env1 uu____15042 orig
                     else
                       (let uu____15048 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15055 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15055 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15048
                        then
                          let uu____15056 =
                            solve_maybe_uinsts env1 orig head1 head2 wl1  in
                          match uu____15056 with
                          | USolved wl2 ->
                              let uu____15058 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [] wl2
                                 in
                              solve env1 uu____15058
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl2 ->
                              solve env1
                                (defer "universe constraints" orig wl2)
                        else
                          (let uu____15062 = base_and_refinement env1 t1  in
                           match uu____15062 with
                           | (base1,refinement1) ->
                               let uu____15087 = base_and_refinement env1 t2
                                  in
                               (match uu____15087 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let uu____15144 =
                                           solve_maybe_uinsts env1 orig head1
                                             head2 wl1
                                            in
                                         (match uu____15144 with
                                          | UFailed msg ->
                                              giveup env1 msg orig
                                          | UDeferred wl2 ->
                                              solve env1
                                                (defer "universe constraints"
                                                   orig wl2)
                                          | USolved wl2 ->
                                              let uu____15148 =
                                                FStar_List.fold_right2
                                                  (fun uu____15181  ->
                                                     fun uu____15182  ->
                                                       fun uu____15183  ->
                                                         match (uu____15181,
                                                                 uu____15182,
                                                                 uu____15183)
                                                         with
                                                         | ((a,uu____15219),
                                                            (a',uu____15221),
                                                            (subprobs,wl3))
                                                             ->
                                                             let uu____15242
                                                               =
                                                               mk_t_problem
                                                                 wl3 [] orig
                                                                 a
                                                                 FStar_TypeChecker_Common.EQ
                                                                 a'
                                                                 FStar_Pervasives_Native.None
                                                                 "index"
                                                                in
                                                             (match uu____15242
                                                              with
                                                              | (p,wl4) ->
                                                                  ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                  args1 args2 ([], wl2)
                                                 in
                                              (match uu____15148 with
                                               | (subprobs,wl3) ->
                                                   ((let uu____15270 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env1)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____15270
                                                     then
                                                       let uu____15271 =
                                                         FStar_Syntax_Print.list_to_string
                                                           (prob_to_string
                                                              env1) subprobs
                                                          in
                                                       FStar_Util.print1
                                                         "Adding subproblems for arguments: %s\n"
                                                         uu____15271
                                                     else ());
                                                    FStar_List.iter
                                                      (def_check_prob
                                                         "solve_t' subprobs")
                                                      subprobs;
                                                    (let formula =
                                                       let uu____15277 =
                                                         FStar_List.map
                                                           p_guard subprobs
                                                          in
                                                       FStar_Syntax_Util.mk_conj_l
                                                         uu____15277
                                                        in
                                                     let wl4 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            formula) [] wl3
                                                        in
                                                     let uu____15285 =
                                                       attempt subprobs wl4
                                                        in
                                                     solve env1 uu____15285))))
                                     | uu____15286 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___184_15326 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___184_15326.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___184_15326.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___184_15326.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___184_15326.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___184_15326.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___184_15326.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___184_15326.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___184_15326.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           (let uu____15364 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____15364
            then
              let uu____15365 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15366 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____15367 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15368 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____15365 uu____15366 uu____15367 uu____15368
            else ());
           (let uu____15370 = head_matches_delta env1 wl1 t1 t2  in
            match uu____15370 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____15401,uu____15402) ->
                     let rec may_relate head3 =
                       let uu____15429 =
                         let uu____15430 = FStar_Syntax_Subst.compress head3
                            in
                         uu____15430.FStar_Syntax_Syntax.n  in
                       match uu____15429 with
                       | FStar_Syntax_Syntax.Tm_name uu____15433 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____15434 -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15457;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_equational_at_level
                               uu____15458;
                             FStar_Syntax_Syntax.fv_qual = uu____15459;_}
                           -> true
                       | FStar_Syntax_Syntax.Tm_fvar
                           { FStar_Syntax_Syntax.fv_name = uu____15462;
                             FStar_Syntax_Syntax.fv_delta =
                               FStar_Syntax_Syntax.Delta_abstract uu____15463;
                             FStar_Syntax_Syntax.fv_qual = uu____15464;_}
                           ->
                           problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____15468,uu____15469) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____15511) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____15517) ->
                           may_relate t
                       | uu____15522 -> false  in
                     let uu____15523 =
                       ((may_relate head1) || (may_relate head2)) &&
                         wl1.smt_ok
                        in
                     if uu____15523
                     then
                       let uu____15524 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15524 with
                        | (guard,wl2) ->
                            let uu____15531 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15531)
                     else
                       (let uu____15533 =
                          let uu____15534 =
                            FStar_Syntax_Print.term_to_string head1  in
                          let uu____15535 =
                            FStar_Syntax_Print.term_to_string head2  in
                          FStar_Util.format2 "head mismatch (%s vs %s)"
                            uu____15534 uu____15535
                           in
                        giveup env1 uu____15533 orig)
                 | (HeadMatch (true ),uu____15536) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____15549 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____15549 with
                        | (guard,wl2) ->
                            let uu____15556 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____15556)
                     else
                       (let uu____15558 =
                          let uu____15559 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____15560 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____15559 uu____15560
                           in
                        giveup env1 uu____15558 orig)
                 | (uu____15561,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___185_15575 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___185_15575.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___185_15575.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___185_15575.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___185_15575.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___185_15575.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___185_15575.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___185_15575.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___185_15575.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif orig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false orig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____15599 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____15599
          then
            let uu____15600 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____15600
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____15605 =
                let uu____15608 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15608  in
              def_check_closed_in (p_loc orig) "ref.t1" uu____15605 t1);
             (let uu____15620 =
                let uu____15623 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____15623  in
              def_check_closed_in (p_loc orig) "ref.t2" uu____15620 t2);
             (let uu____15635 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____15635
              then
                let uu____15636 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____15637 =
                  let uu____15638 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____15639 =
                    let uu____15640 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____15640  in
                  Prims.strcat uu____15638 uu____15639  in
                let uu____15641 =
                  let uu____15642 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____15643 =
                    let uu____15644 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____15644  in
                  Prims.strcat uu____15642 uu____15643  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____15636
                  uu____15637 uu____15641
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____15647,uu____15648) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____15673,FStar_Syntax_Syntax.Tm_delayed uu____15674) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____15699,uu____15700) ->
                  let uu____15727 =
                    let uu___186_15728 = problem  in
                    let uu____15729 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___186_15728.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15729;
                      FStar_TypeChecker_Common.relation =
                        (uu___186_15728.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___186_15728.FStar_TypeChecker_Common.rhs);
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
              | (FStar_Syntax_Syntax.Tm_meta uu____15730,uu____15731) ->
                  let uu____15738 =
                    let uu___187_15739 = problem  in
                    let uu____15740 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___187_15739.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____15740;
                      FStar_TypeChecker_Common.relation =
                        (uu___187_15739.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___187_15739.FStar_TypeChecker_Common.rhs);
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
              | (uu____15741,FStar_Syntax_Syntax.Tm_ascribed uu____15742) ->
                  let uu____15769 =
                    let uu___188_15770 = problem  in
                    let uu____15771 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___188_15770.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___188_15770.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___188_15770.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15771;
                      FStar_TypeChecker_Common.element =
                        (uu___188_15770.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___188_15770.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___188_15770.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___188_15770.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___188_15770.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___188_15770.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15769 wl
              | (uu____15772,FStar_Syntax_Syntax.Tm_meta uu____15773) ->
                  let uu____15780 =
                    let uu___189_15781 = problem  in
                    let uu____15782 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___189_15781.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___189_15781.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___189_15781.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____15782;
                      FStar_TypeChecker_Common.element =
                        (uu___189_15781.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___189_15781.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___189_15781.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___189_15781.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___189_15781.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___189_15781.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____15780 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____15784),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____15786)) ->
                  let uu____15795 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____15795
              | (FStar_Syntax_Syntax.Tm_bvar uu____15796,uu____15797) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____15798,FStar_Syntax_Syntax.Tm_bvar uu____15799) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___144_15858 =
                    match uu___144_15858 with
                    | [] -> c
                    | bs ->
                        let uu____15880 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15880
                     in
                  let uu____15889 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15889 with
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
                                    let uu____16012 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____16012
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
                  let mk_t t l uu___145_16087 =
                    match uu___145_16087 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____16121 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____16121 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____16240 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____16241 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____16240
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____16241 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____16242,uu____16243) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16270 -> true
                    | uu____16287 -> false  in
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
                      (let uu____16328 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___190_16336 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___190_16336.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___190_16336.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___190_16336.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___190_16336.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___190_16336.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___190_16336.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___190_16336.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___190_16336.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___190_16336.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___190_16336.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___190_16336.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___190_16336.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___190_16336.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___190_16336.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___190_16336.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___190_16336.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___190_16336.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___190_16336.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___190_16336.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___190_16336.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___190_16336.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___190_16336.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___190_16336.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___190_16336.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___190_16336.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___190_16336.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___190_16336.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___190_16336.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___190_16336.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___190_16336.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___190_16336.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___190_16336.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___190_16336.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___190_16336.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___190_16336.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___190_16336.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16328 with
                       | (uu____16339,ty,uu____16341) ->
                           let uu____16342 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16342)
                     in
                  let uu____16343 =
                    let uu____16356 = maybe_eta t1  in
                    let uu____16361 = maybe_eta t2  in
                    (uu____16356, uu____16361)  in
                  (match uu____16343 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___191_16385 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___191_16385.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___191_16385.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___191_16385.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___191_16385.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___191_16385.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___191_16385.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___191_16385.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___191_16385.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16396 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16396
                       then
                         let uu____16397 = destruct_flex_t not_abs wl  in
                         (match uu____16397 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16412 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16412.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16412.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16412.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16412.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16412.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16412.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16412.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16412.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16424 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16424
                       then
                         let uu____16425 = destruct_flex_t not_abs wl  in
                         (match uu____16425 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16440 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16440.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16440.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16440.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16440.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16440.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16440.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16440.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16440.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16442 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____16455,FStar_Syntax_Syntax.Tm_abs uu____16456) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____16483 -> true
                    | uu____16500 -> false  in
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
                      (let uu____16541 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___190_16549 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___190_16549.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___190_16549.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___190_16549.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___190_16549.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___190_16549.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___190_16549.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___190_16549.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___190_16549.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___190_16549.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___190_16549.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___190_16549.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___190_16549.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___190_16549.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___190_16549.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___190_16549.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___190_16549.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___190_16549.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___190_16549.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___190_16549.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___190_16549.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___190_16549.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___190_16549.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___190_16549.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___190_16549.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___190_16549.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___190_16549.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___190_16549.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___190_16549.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___190_16549.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___190_16549.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___190_16549.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___190_16549.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___190_16549.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___190_16549.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___190_16549.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___190_16549.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____16541 with
                       | (uu____16552,ty,uu____16554) ->
                           let uu____16555 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____16555)
                     in
                  let uu____16556 =
                    let uu____16569 = maybe_eta t1  in
                    let uu____16574 = maybe_eta t2  in
                    (uu____16569, uu____16574)  in
                  (match uu____16556 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___191_16598 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___191_16598.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___191_16598.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___191_16598.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___191_16598.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___191_16598.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___191_16598.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___191_16598.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___191_16598.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____16609 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16609
                       then
                         let uu____16610 = destruct_flex_t not_abs wl  in
                         (match uu____16610 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16625 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16625.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16625.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16625.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16625.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16625.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16625.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16625.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16625.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____16637 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____16637
                       then
                         let uu____16638 = destruct_flex_t not_abs wl  in
                         (match uu____16638 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___192_16653 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___192_16653.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___192_16653.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___192_16653.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___192_16653.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___192_16653.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___192_16653.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___192_16653.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___192_16653.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____16655 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____16683 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____16683) &&
                       (let uu____16687 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____16687))
                      &&
                      (let uu____16694 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____16694 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___146_16706 =
                             match uu___146_16706 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____16707 -> true
                             | uu____16708 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____16709 -> false)
                     in
                  let uu____16710 = as_refinement should_delta env wl t1  in
                  (match uu____16710 with
                   | (x11,phi1) ->
                       let uu____16717 = as_refinement should_delta env wl t2
                          in
                       (match uu____16717 with
                        | (x21,phi21) ->
                            let uu____16724 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____16724 with
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
                                   let uu____16790 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____16790
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____16802 =
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
                                   (let uu____16813 =
                                      let uu____16816 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16816
                                       in
                                    def_check_closed_in (p_loc orig) "ref.1"
                                      uu____16813 (p_guard base_prob));
                                   (let uu____16828 =
                                      let uu____16831 = p_scope orig  in
                                      FStar_List.map
                                        FStar_Pervasives_Native.fst
                                        uu____16831
                                       in
                                    def_check_closed_in (p_loc orig) "ref.2"
                                      uu____16828 impl);
                                   (let wl2 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl1
                                       in
                                    let uu____16843 = attempt [base_prob] wl2
                                       in
                                    solve env1 uu____16843)
                                    in
                                 let has_uvars =
                                   (let uu____16847 =
                                      let uu____16848 =
                                        FStar_Syntax_Free.uvars phi11  in
                                      FStar_Util.set_is_empty uu____16848  in
                                    Prims.op_Negation uu____16847) ||
                                     (let uu____16852 =
                                        let uu____16853 =
                                          FStar_Syntax_Free.uvars phi22  in
                                        FStar_Util.set_is_empty uu____16853
                                         in
                                      Prims.op_Negation uu____16852)
                                    in
                                 if
                                   (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     ||
                                     ((Prims.op_Negation
                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                        && has_uvars)
                                 then
                                   let uu____16856 =
                                     let uu____16861 =
                                       let uu____16868 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16868]  in
                                     mk_t_problem wl1 uu____16861 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16856 with
                                    | (ref_prob,wl2) ->
                                        let uu____16883 =
                                          solve env1
                                            (let uu___193_16885 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___193_16885.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___193_16885.smt_ok);
                                               tcenv = (uu___193_16885.tcenv);
                                               wl_implicits =
                                                 (uu___193_16885.wl_implicits)
                                             })
                                           in
                                        (match uu____16883 with
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
                                         | Success uu____16895 ->
                                             let guard =
                                               let uu____16903 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16903
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___194_16912 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___194_16912.attempting);
                                                 wl_deferred =
                                                   (uu___194_16912.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___194_16912.defer_ok);
                                                 smt_ok =
                                                   (uu___194_16912.smt_ok);
                                                 tcenv =
                                                   (uu___194_16912.tcenv);
                                                 wl_implicits =
                                                   (uu___194_16912.wl_implicits)
                                               }  in
                                             let uu____16913 =
                                               attempt [base_prob] wl4  in
                                             solve env1 uu____16913))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16915,FStar_Syntax_Syntax.Tm_uvar uu____16916) ->
                  let uu____16945 = destruct_flex_t t1 wl  in
                  (match uu____16945 with
                   | (f1,wl1) ->
                       let uu____16952 = destruct_flex_t t2 wl1  in
                       (match uu____16952 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16959;
                    FStar_Syntax_Syntax.pos = uu____16960;
                    FStar_Syntax_Syntax.vars = uu____16961;_},uu____16962),FStar_Syntax_Syntax.Tm_uvar
                 uu____16963) ->
                  let uu____17012 = destruct_flex_t t1 wl  in
                  (match uu____17012 with
                   | (f1,wl1) ->
                       let uu____17019 = destruct_flex_t t2 wl1  in
                       (match uu____17019 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17026,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17027;
                    FStar_Syntax_Syntax.pos = uu____17028;
                    FStar_Syntax_Syntax.vars = uu____17029;_},uu____17030))
                  ->
                  let uu____17079 = destruct_flex_t t1 wl  in
                  (match uu____17079 with
                   | (f1,wl1) ->
                       let uu____17086 = destruct_flex_t t2 wl1  in
                       (match uu____17086 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17093;
                    FStar_Syntax_Syntax.pos = uu____17094;
                    FStar_Syntax_Syntax.vars = uu____17095;_},uu____17096),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17097;
                    FStar_Syntax_Syntax.pos = uu____17098;
                    FStar_Syntax_Syntax.vars = uu____17099;_},uu____17100))
                  ->
                  let uu____17169 = destruct_flex_t t1 wl  in
                  (match uu____17169 with
                   | (f1,wl1) ->
                       let uu____17176 = destruct_flex_t t2 wl1  in
                       (match uu____17176 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____17183,uu____17184) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17199 = destruct_flex_t t1 wl  in
                  (match uu____17199 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17206;
                    FStar_Syntax_Syntax.pos = uu____17207;
                    FStar_Syntax_Syntax.vars = uu____17208;_},uu____17209),uu____17210)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____17245 = destruct_flex_t t1 wl  in
                  (match uu____17245 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____17252,FStar_Syntax_Syntax.Tm_uvar uu____17253) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____17268,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17269;
                    FStar_Syntax_Syntax.pos = uu____17270;
                    FStar_Syntax_Syntax.vars = uu____17271;_},uu____17272))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____17307,FStar_Syntax_Syntax.Tm_arrow uu____17308) ->
                  solve_t' env
                    (let uu___195_17336 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17336.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17336.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17336.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17336.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17336.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17336.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17336.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17336.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17336.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17337;
                    FStar_Syntax_Syntax.pos = uu____17338;
                    FStar_Syntax_Syntax.vars = uu____17339;_},uu____17340),FStar_Syntax_Syntax.Tm_arrow
                 uu____17341) ->
                  solve_t' env
                    (let uu___195_17389 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___195_17389.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___195_17389.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___195_17389.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___195_17389.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___195_17389.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___195_17389.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___195_17389.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___195_17389.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___195_17389.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17390,FStar_Syntax_Syntax.Tm_uvar uu____17391) ->
                  let uu____17406 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17406
              | (uu____17407,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17408;
                    FStar_Syntax_Syntax.pos = uu____17409;
                    FStar_Syntax_Syntax.vars = uu____17410;_},uu____17411))
                  ->
                  let uu____17446 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17446
              | (FStar_Syntax_Syntax.Tm_uvar uu____17447,uu____17448) ->
                  let uu____17463 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17463
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____17464;
                    FStar_Syntax_Syntax.pos = uu____17465;
                    FStar_Syntax_Syntax.vars = uu____17466;_},uu____17467),uu____17468)
                  ->
                  let uu____17503 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____17503
              | (FStar_Syntax_Syntax.Tm_refine uu____17504,uu____17505) ->
                  let t21 =
                    let uu____17513 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____17513  in
                  solve_t env
                    (let uu___196_17539 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___196_17539.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___196_17539.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___196_17539.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___196_17539.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___196_17539.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___196_17539.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___196_17539.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___196_17539.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___196_17539.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____17540,FStar_Syntax_Syntax.Tm_refine uu____17541) ->
                  let t11 =
                    let uu____17549 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____17549  in
                  solve_t env
                    (let uu___197_17575 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___197_17575.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___197_17575.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___197_17575.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___197_17575.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___197_17575.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___197_17575.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___197_17575.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___197_17575.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___197_17575.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____17657 =
                    let uu____17658 = guard_of_prob env wl problem t1 t2  in
                    match uu____17658 with
                    | (guard,wl1) ->
                        let uu____17665 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____17665
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____17876 = br1  in
                        (match uu____17876 with
                         | (p1,w1,uu____17901) ->
                             let uu____17918 = br2  in
                             (match uu____17918 with
                              | (p2,w2,uu____17937) ->
                                  let uu____17942 =
                                    let uu____17943 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____17943  in
                                  if uu____17942
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____17959 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____17959 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____17992 = br2  in
                                         (match uu____17992 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____18027 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____18027
                                                 in
                                              let uu____18038 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____18061,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____18078) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____18121 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____18121 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([p], wl2))
                                                 in
                                              FStar_Util.bind_opt uu____18038
                                                (fun uu____18163  ->
                                                   match uu____18163 with
                                                   | (wprobs,wl2) ->
                                                       let uu____18184 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____18184
                                                        with
                                                        | (prob,wl3) ->
                                                            let uu____18199 =
                                                              solve_branches
                                                                wl3 rs1 rs2
                                                               in
                                                            FStar_Util.bind_opt
                                                              uu____18199
                                                              (fun
                                                                 uu____18223 
                                                                 ->
                                                                 match uu____18223
                                                                 with
                                                                 | (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____18308 -> FStar_Pervasives_Native.None  in
                  let uu____18345 = solve_branches wl brs1 brs2  in
                  (match uu____18345 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____18373 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____18373 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let formula =
                              let uu____18390 =
                                FStar_List.map (fun p  -> p_guard p)
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____18390  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____18399 =
                              let uu____18400 =
                                attempt sub_probs1
                                  (let uu___198_18402 = wl3  in
                                   {
                                     attempting = (uu___198_18402.attempting);
                                     wl_deferred =
                                       (uu___198_18402.wl_deferred);
                                     ctr = (uu___198_18402.ctr);
                                     defer_ok = (uu___198_18402.defer_ok);
                                     smt_ok = false;
                                     tcenv = (uu___198_18402.tcenv);
                                     wl_implicits =
                                       (uu___198_18402.wl_implicits)
                                   })
                                 in
                              solve env uu____18400  in
                            (match uu____18399 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____18406 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____18412,uu____18413) ->
                  let head1 =
                    let uu____18437 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18437
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18477 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18477
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18517 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18517
                    then
                      let uu____18518 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18519 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18520 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18518 uu____18519 uu____18520
                    else ());
                   (let uu____18522 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18522
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18529 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18529
                       then
                         let uu____18530 =
                           let uu____18537 =
                             let uu____18538 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18538 = FStar_Syntax_Util.Equal  in
                           if uu____18537
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18548 = mk_eq2 wl orig t1 t2  in
                              match uu____18548 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18530 with
                         | (guard,wl1) ->
                             let uu____18569 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18569
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____18572,uu____18573) ->
                  let head1 =
                    let uu____18581 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18581
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18621 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18621
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18661 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18661
                    then
                      let uu____18662 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18663 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18664 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18662 uu____18663 uu____18664
                    else ());
                   (let uu____18666 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18666
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18673 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18673
                       then
                         let uu____18674 =
                           let uu____18681 =
                             let uu____18682 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18682 = FStar_Syntax_Util.Equal  in
                           if uu____18681
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18692 = mk_eq2 wl orig t1 t2  in
                              match uu____18692 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18674 with
                         | (guard,wl1) ->
                             let uu____18713 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18713
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____18716,uu____18717) ->
                  let head1 =
                    let uu____18719 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18719
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18759 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18759
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18799 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18799
                    then
                      let uu____18800 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18801 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18802 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18800 uu____18801 uu____18802
                    else ());
                   (let uu____18804 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18804
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18811 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18811
                       then
                         let uu____18812 =
                           let uu____18819 =
                             let uu____18820 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18820 = FStar_Syntax_Util.Equal  in
                           if uu____18819
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18830 = mk_eq2 wl orig t1 t2  in
                              match uu____18830 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18812 with
                         | (guard,wl1) ->
                             let uu____18851 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18851
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____18854,uu____18855) ->
                  let head1 =
                    let uu____18857 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18857
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18897 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18897
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18937 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18937
                    then
                      let uu____18938 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18939 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18940 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18938 uu____18939 uu____18940
                    else ());
                   (let uu____18942 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18942
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18949 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18949
                       then
                         let uu____18950 =
                           let uu____18957 =
                             let uu____18958 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18958 = FStar_Syntax_Util.Equal  in
                           if uu____18957
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18968 = mk_eq2 wl orig t1 t2  in
                              match uu____18968 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18950 with
                         | (guard,wl1) ->
                             let uu____18989 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18989
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____18992,uu____18993) ->
                  let head1 =
                    let uu____18995 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18995
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19035 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19035
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19075 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19075
                    then
                      let uu____19076 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19077 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19078 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19076 uu____19077 uu____19078
                    else ());
                   (let uu____19080 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19080
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19087 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19087
                       then
                         let uu____19088 =
                           let uu____19095 =
                             let uu____19096 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19096 = FStar_Syntax_Util.Equal  in
                           if uu____19095
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19106 = mk_eq2 wl orig t1 t2  in
                              match uu____19106 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19088 with
                         | (guard,wl1) ->
                             let uu____19127 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19127
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____19130,uu____19131) ->
                  let head1 =
                    let uu____19147 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19147
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19187 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19187
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19227 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19227
                    then
                      let uu____19228 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19229 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19230 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19228 uu____19229 uu____19230
                    else ());
                   (let uu____19232 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19232
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19239 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19239
                       then
                         let uu____19240 =
                           let uu____19247 =
                             let uu____19248 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19248 = FStar_Syntax_Util.Equal  in
                           if uu____19247
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19258 = mk_eq2 wl orig t1 t2  in
                              match uu____19258 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19240 with
                         | (guard,wl1) ->
                             let uu____19279 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19279
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19282,FStar_Syntax_Syntax.Tm_match uu____19283) ->
                  let head1 =
                    let uu____19307 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19307
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19347 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19347
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19387 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19387
                    then
                      let uu____19388 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19389 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19390 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19388 uu____19389 uu____19390
                    else ());
                   (let uu____19392 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19392
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19399 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19399
                       then
                         let uu____19400 =
                           let uu____19407 =
                             let uu____19408 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19408 = FStar_Syntax_Util.Equal  in
                           if uu____19407
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19418 = mk_eq2 wl orig t1 t2  in
                              match uu____19418 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19400 with
                         | (guard,wl1) ->
                             let uu____19439 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19439
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19442,FStar_Syntax_Syntax.Tm_uinst uu____19443) ->
                  let head1 =
                    let uu____19451 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19451
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19491 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19491
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19531 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19531
                    then
                      let uu____19532 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19533 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19534 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19532 uu____19533 uu____19534
                    else ());
                   (let uu____19536 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19536
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19543 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19543
                       then
                         let uu____19544 =
                           let uu____19551 =
                             let uu____19552 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19552 = FStar_Syntax_Util.Equal  in
                           if uu____19551
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19562 = mk_eq2 wl orig t1 t2  in
                              match uu____19562 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19544 with
                         | (guard,wl1) ->
                             let uu____19583 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19583
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19586,FStar_Syntax_Syntax.Tm_name uu____19587) ->
                  let head1 =
                    let uu____19589 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19589
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19629 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19629
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19669 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19669
                    then
                      let uu____19670 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19671 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19672 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19670 uu____19671 uu____19672
                    else ());
                   (let uu____19674 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19674
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19681 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19681
                       then
                         let uu____19682 =
                           let uu____19689 =
                             let uu____19690 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19690 = FStar_Syntax_Util.Equal  in
                           if uu____19689
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19700 = mk_eq2 wl orig t1 t2  in
                              match uu____19700 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19682 with
                         | (guard,wl1) ->
                             let uu____19721 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19721
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19724,FStar_Syntax_Syntax.Tm_constant uu____19725) ->
                  let head1 =
                    let uu____19727 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19727
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19767 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19767
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19807 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19807
                    then
                      let uu____19808 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19809 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19810 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19808 uu____19809 uu____19810
                    else ());
                   (let uu____19812 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19812
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19819 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19819
                       then
                         let uu____19820 =
                           let uu____19827 =
                             let uu____19828 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19828 = FStar_Syntax_Util.Equal  in
                           if uu____19827
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19838 = mk_eq2 wl orig t1 t2  in
                              match uu____19838 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19820 with
                         | (guard,wl1) ->
                             let uu____19859 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19859
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____19862,FStar_Syntax_Syntax.Tm_fvar uu____19863) ->
                  let head1 =
                    let uu____19865 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____19865
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19905 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19905
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19945 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19945
                    then
                      let uu____19946 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19947 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19948 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19946 uu____19947 uu____19948
                    else ());
                   (let uu____19950 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19950
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19957 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19957
                       then
                         let uu____19958 =
                           let uu____19965 =
                             let uu____19966 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19966 = FStar_Syntax_Util.Equal  in
                           if uu____19965
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19976 = mk_eq2 wl orig t1 t2  in
                              match uu____19976 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19958 with
                         | (guard,wl1) ->
                             let uu____19997 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19997
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____20000,FStar_Syntax_Syntax.Tm_app uu____20001) ->
                  let head1 =
                    let uu____20017 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____20017
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____20057 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____20057
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____20097 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____20097
                    then
                      let uu____20098 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____20099 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____20100 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____20098 uu____20099 uu____20100
                    else ());
                   (let uu____20102 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____20102
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____20109 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____20109
                       then
                         let uu____20110 =
                           let uu____20117 =
                             let uu____20118 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____20118 = FStar_Syntax_Util.Equal  in
                           if uu____20117
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____20128 = mk_eq2 wl orig t1 t2  in
                              match uu____20128 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____20110 with
                         | (guard,wl1) ->
                             let uu____20149 = solve_prob orig guard [] wl1
                                in
                             solve env uu____20149
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____20152,FStar_Syntax_Syntax.Tm_let uu____20153) ->
                  let uu____20178 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____20178
                  then
                    let uu____20179 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____20179
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____20181,uu____20182) ->
                  let uu____20195 =
                    let uu____20200 =
                      let uu____20201 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20202 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20203 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20204 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20201 uu____20202 uu____20203 uu____20204
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20200)
                     in
                  FStar_Errors.raise_error uu____20195
                    t1.FStar_Syntax_Syntax.pos
              | (uu____20205,FStar_Syntax_Syntax.Tm_let uu____20206) ->
                  let uu____20219 =
                    let uu____20224 =
                      let uu____20225 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____20226 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____20227 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____20228 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____20225 uu____20226 uu____20227 uu____20228
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____20224)
                     in
                  FStar_Errors.raise_error uu____20219
                    t1.FStar_Syntax_Syntax.pos
              | uu____20229 -> giveup env "head tag mismatch" orig))))

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
          (let uu____20288 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____20288
           then
             let uu____20289 =
               let uu____20290 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____20290  in
             let uu____20291 =
               let uu____20292 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____20292  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____20289 uu____20291
           else ());
          (let uu____20294 =
             let uu____20295 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____20295  in
           if uu____20294
           then
             let uu____20296 =
               let uu____20297 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____20298 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____20297 uu____20298
                in
             giveup env uu____20296 orig
           else
             (let uu____20300 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____20300 with
              | (ret_sub_prob,wl1) ->
                  let uu____20307 =
                    FStar_List.fold_right2
                      (fun uu____20340  ->
                         fun uu____20341  ->
                           fun uu____20342  ->
                             match (uu____20340, uu____20341, uu____20342)
                             with
                             | ((a1,uu____20378),(a2,uu____20380),(arg_sub_probs,wl2))
                                 ->
                                 let uu____20401 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____20401 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____20307 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____20430 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____20430  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____20438 = attempt sub_probs wl3  in
                       solve env uu____20438)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____20461 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____20464)::[] -> wp1
              | uu____20481 ->
                  let uu____20490 =
                    let uu____20491 =
                      let uu____20492 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____20492  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____20491
                     in
                  failwith uu____20490
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____20498 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____20498]
              | x -> x  in
            let uu____20500 =
              let uu____20509 =
                let uu____20516 =
                  let uu____20517 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____20517 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____20516  in
              [uu____20509]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____20500;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____20530 = lift_c1 ()  in solve_eq uu____20530 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___147_20536  ->
                       match uu___147_20536 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____20537 -> false))
                in
             let uu____20538 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____20564)::uu____20565,(wp2,uu____20567)::uu____20568)
                   -> (wp1, wp2)
               | uu____20621 ->
                   let uu____20642 =
                     let uu____20647 =
                       let uu____20648 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____20649 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____20648 uu____20649
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____20647)
                      in
                   FStar_Errors.raise_error uu____20642
                     env.FStar_TypeChecker_Env.range
                in
             match uu____20538 with
             | (wpc1,wpc2) ->
                 let uu____20656 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____20656
                 then
                   let uu____20659 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____20659 wl
                 else
                   (let uu____20661 =
                      let uu____20668 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____20668  in
                    match uu____20661 with
                    | (c2_decl,qualifiers) ->
                        let uu____20689 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____20689
                        then
                          let c1_repr =
                            let uu____20693 =
                              let uu____20694 =
                                let uu____20695 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____20695  in
                              let uu____20696 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20694 uu____20696
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20693
                             in
                          let c2_repr =
                            let uu____20698 =
                              let uu____20699 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____20700 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____20699 uu____20700
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____20698
                             in
                          let uu____20701 =
                            let uu____20706 =
                              let uu____20707 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____20708 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____20707 uu____20708
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____20706
                             in
                          (match uu____20701 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____20712 = attempt [prob] wl2  in
                               solve env uu____20712)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____20723 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____20723
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____20726 =
                                     let uu____20733 =
                                       let uu____20734 =
                                         let uu____20749 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____20752 =
                                           let uu____20761 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____20768 =
                                             let uu____20777 =
                                               let uu____20784 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____20784
                                                in
                                             [uu____20777]  in
                                           uu____20761 :: uu____20768  in
                                         (uu____20749, uu____20752)  in
                                       FStar_Syntax_Syntax.Tm_app uu____20734
                                        in
                                     FStar_Syntax_Syntax.mk uu____20733  in
                                   uu____20726 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____20819 =
                                    let uu____20826 =
                                      let uu____20827 =
                                        let uu____20842 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____20845 =
                                          let uu____20854 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____20861 =
                                            let uu____20870 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____20877 =
                                              let uu____20886 =
                                                let uu____20893 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____20893
                                                 in
                                              [uu____20886]  in
                                            uu____20870 :: uu____20877  in
                                          uu____20854 :: uu____20861  in
                                        (uu____20842, uu____20845)  in
                                      FStar_Syntax_Syntax.Tm_app uu____20827
                                       in
                                    FStar_Syntax_Syntax.mk uu____20826  in
                                  uu____20819 FStar_Pervasives_Native.None r)
                              in
                           let uu____20931 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____20931 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____20939 =
                                   let uu____20942 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_24  ->
                                        FStar_Pervasives_Native.Some _0_24)
                                     uu____20942
                                    in
                                 solve_prob orig uu____20939 [] wl1  in
                               let uu____20949 = attempt [base_prob] wl2  in
                               solve env uu____20949)))
           in
        let uu____20950 = FStar_Util.physical_equality c1 c2  in
        if uu____20950
        then
          let uu____20951 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____20951
        else
          ((let uu____20954 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____20954
            then
              let uu____20955 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____20956 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____20955
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____20956
            else ());
           (let uu____20958 =
              let uu____20967 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____20970 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____20967, uu____20970)  in
            match uu____20958 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20988),FStar_Syntax_Syntax.Total
                    (t2,uu____20990)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____21007 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21007 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21008,FStar_Syntax_Syntax.Total uu____21009) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21027),FStar_Syntax_Syntax.Total
                    (t2,uu____21029)) ->
                     let uu____21046 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21046 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____21048),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21050)) ->
                     let uu____21067 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21067 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____21069),FStar_Syntax_Syntax.GTotal
                    (t2,uu____21071)) ->
                     let uu____21088 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____21088 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____21089,FStar_Syntax_Syntax.Comp uu____21090) ->
                     let uu____21099 =
                       let uu___199_21102 = problem  in
                       let uu____21105 =
                         let uu____21106 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21106
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_21102.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21105;
                         FStar_TypeChecker_Common.relation =
                           (uu___199_21102.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___199_21102.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___199_21102.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_21102.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_21102.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_21102.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_21102.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_21102.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21099 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____21107,FStar_Syntax_Syntax.Comp uu____21108) ->
                     let uu____21117 =
                       let uu___199_21120 = problem  in
                       let uu____21123 =
                         let uu____21124 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21124
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___199_21120.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____21123;
                         FStar_TypeChecker_Common.relation =
                           (uu___199_21120.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___199_21120.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___199_21120.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___199_21120.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___199_21120.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___199_21120.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___199_21120.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___199_21120.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21117 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21125,FStar_Syntax_Syntax.GTotal uu____21126) ->
                     let uu____21135 =
                       let uu___200_21138 = problem  in
                       let uu____21141 =
                         let uu____21142 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21142
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_21138.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___200_21138.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___200_21138.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21141;
                         FStar_TypeChecker_Common.element =
                           (uu___200_21138.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_21138.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_21138.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_21138.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_21138.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_21138.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21135 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21143,FStar_Syntax_Syntax.Total uu____21144) ->
                     let uu____21153 =
                       let uu___200_21156 = problem  in
                       let uu____21159 =
                         let uu____21160 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____21160
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___200_21156.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___200_21156.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___200_21156.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____21159;
                         FStar_TypeChecker_Common.element =
                           (uu___200_21156.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___200_21156.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___200_21156.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___200_21156.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___200_21156.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___200_21156.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____21153 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____21161,FStar_Syntax_Syntax.Comp uu____21162) ->
                     let uu____21163 =
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
                     if uu____21163
                     then
                       let uu____21164 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____21164 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____21168 =
                            let uu____21173 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____21173
                            then (c1_comp, c2_comp)
                            else
                              (let uu____21179 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____21180 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____21179, uu____21180))
                             in
                          match uu____21168 with
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
                           (let uu____21187 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____21187
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____21189 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____21189 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21192 =
                                  let uu____21193 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____21194 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____21193 uu____21194
                                   in
                                giveup env uu____21192 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____21201 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____21229  ->
              match uu____21229 with
              | (uu____21238,tm,uu____21240,uu____21241) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____21201 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____21274 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____21274 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____21292 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____21320  ->
                match uu____21320 with
                | (u1,u2) ->
                    let uu____21327 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____21328 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____21327 uu____21328))
         in
      FStar_All.pipe_right uu____21292 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____21355,[])) -> "{}"
      | uu____21380 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____21403 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____21403
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____21406 =
              FStar_List.map
                (fun uu____21416  ->
                   match uu____21416 with
                   | (uu____21421,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____21406 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____21426 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____21426 imps
  
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
                  let uu____21479 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____21479
                  then
                    let uu____21480 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____21481 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____21480
                      (rel_to_string rel) uu____21481
                  else "TOP"  in
                let uu____21483 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____21483 with
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
              let uu____21541 =
                let uu____21544 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_25  -> FStar_Pervasives_Native.Some _0_25)
                  uu____21544
                 in
              FStar_Syntax_Syntax.new_bv uu____21541 t1  in
            let uu____21547 =
              let uu____21552 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____21552
               in
            match uu____21547 with | (p,wl1) -> (p, x, wl1)
  
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
            ((let uu____21625 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____21625
              then
                let uu____21626 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____21626
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
          ((let uu____21648 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____21648
            then
              let uu____21649 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____21649
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____21653 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____21653
             then
               let uu____21654 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____21654
             else ());
            (let f2 =
               let uu____21657 =
                 let uu____21658 = FStar_Syntax_Util.unmeta f1  in
                 uu____21658.FStar_Syntax_Syntax.n  in
               match uu____21657 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____21662 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___201_21663 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___201_21663.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___201_21663.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___201_21663.FStar_TypeChecker_Env.implicits)
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
            let uu____21765 =
              let uu____21766 =
                let uu____21767 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____21767;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____21766  in
            FStar_All.pipe_left
              (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____21765
  
let with_guard_no_simp :
  'Auu____21782 .
    'Auu____21782 ->
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
            let uu____21805 =
              let uu____21806 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____21806;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____21805
  
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
          (let uu____21844 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____21844
           then
             let uu____21845 = FStar_Syntax_Print.term_to_string t1  in
             let uu____21846 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____21845
               uu____21846
           else ());
          (let uu____21848 =
             let uu____21853 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____21853
              in
           match uu____21848 with
           | (prob,wl) ->
               let g =
                 let uu____21861 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____21879  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____21861  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21921 = try_teq true env t1 t2  in
        match uu____21921 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____21925 = FStar_TypeChecker_Env.get_range env  in
              let uu____21926 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____21925 uu____21926);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____21933 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____21933
              then
                let uu____21934 = FStar_Syntax_Print.term_to_string t1  in
                let uu____21935 = FStar_Syntax_Print.term_to_string t2  in
                let uu____21936 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____21934
                  uu____21935 uu____21936
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
          let uu____21958 = FStar_TypeChecker_Env.get_range env  in
          let uu____21959 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____21958 uu____21959
  
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
        (let uu____21984 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21984
         then
           let uu____21985 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____21986 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____21985 uu____21986
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____21989 =
           let uu____21996 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____21996 "sub_comp"
            in
         match uu____21989 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____22007 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____22025  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____22007)))
  
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
      fun uu____22078  ->
        match uu____22078 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____22121 =
                 let uu____22126 =
                   let uu____22127 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____22128 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____22127 uu____22128
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____22126)  in
               let uu____22129 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____22121 uu____22129)
               in
            let equiv1 v1 v' =
              let uu____22141 =
                let uu____22146 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____22147 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____22146, uu____22147)  in
              match uu____22141 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____22166 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____22196 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____22196 with
                      | FStar_Syntax_Syntax.U_unif uu____22203 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____22232  ->
                                    match uu____22232 with
                                    | (u,v') ->
                                        let uu____22241 = equiv1 v1 v'  in
                                        if uu____22241
                                        then
                                          let uu____22244 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____22244 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____22260 -> []))
               in
            let uu____22265 =
              let wl =
                let uu___202_22269 = empty_worklist env  in
                {
                  attempting = (uu___202_22269.attempting);
                  wl_deferred = (uu___202_22269.wl_deferred);
                  ctr = (uu___202_22269.ctr);
                  defer_ok = false;
                  smt_ok = (uu___202_22269.smt_ok);
                  tcenv = (uu___202_22269.tcenv);
                  wl_implicits = (uu___202_22269.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____22287  ->
                      match uu____22287 with
                      | (lb,v1) ->
                          let uu____22294 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____22294 with
                           | USolved wl1 -> ()
                           | uu____22296 -> fail1 lb v1)))
               in
            let rec check_ineq uu____22306 =
              match uu____22306 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____22315) -> true
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
                      uu____22338,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____22340,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____22351) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____22358,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____22366 -> false)
               in
            let uu____22371 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____22386  ->
                      match uu____22386 with
                      | (u,v1) ->
                          let uu____22393 = check_ineq (u, v1)  in
                          if uu____22393
                          then true
                          else
                            ((let uu____22396 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____22396
                              then
                                let uu____22397 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____22398 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____22397
                                  uu____22398
                              else ());
                             false)))
               in
            if uu____22371
            then ()
            else
              ((let uu____22402 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____22402
                then
                  ((let uu____22404 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____22404);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____22414 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____22414))
                else ());
               (let uu____22424 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____22424))
  
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
        let fail1 uu____22491 =
          match uu____22491 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___203_22512 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___203_22512.attempting);
            wl_deferred = (uu___203_22512.wl_deferred);
            ctr = (uu___203_22512.ctr);
            defer_ok;
            smt_ok = (uu___203_22512.smt_ok);
            tcenv = (uu___203_22512.tcenv);
            wl_implicits = (uu___203_22512.wl_implicits)
          }  in
        (let uu____22514 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22514
         then
           let uu____22515 = FStar_Util.string_of_bool defer_ok  in
           let uu____22516 = wl_to_string wl  in
           let uu____22517 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____22515 uu____22516 uu____22517
         else ());
        (let g1 =
           let uu____22528 = solve_and_commit env wl fail1  in
           match uu____22528 with
           | FStar_Pervasives_Native.Some
               (uu____22535::uu____22536,uu____22537) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___204_22562 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___204_22562.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___204_22562.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____22571 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___205_22579 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___205_22579.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___205_22579.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___205_22579.FStar_TypeChecker_Env.implicits)
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
    let uu____22627 = FStar_ST.op_Bang last_proof_ns  in
    match uu____22627 with
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
            let uu___206_22750 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___206_22750.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___206_22750.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___206_22750.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____22751 =
            let uu____22752 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____22752  in
          if uu____22751
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____22760 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____22761 =
                       let uu____22762 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____22762
                        in
                     FStar_Errors.diag uu____22760 uu____22761)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____22766 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____22767 =
                        let uu____22768 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____22768
                         in
                      FStar_Errors.diag uu____22766 uu____22767)
                   else ();
                   (let uu____22771 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____22771 "discharge_guard'"
                      env vc1);
                   (let uu____22772 = check_trivial vc1  in
                    match uu____22772 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____22779 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22780 =
                                let uu____22781 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____22781
                                 in
                              FStar_Errors.diag uu____22779 uu____22780)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____22786 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____22787 =
                                let uu____22788 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____22788
                                 in
                              FStar_Errors.diag uu____22786 uu____22787)
                           else ();
                           (let vcs =
                              let uu____22801 = FStar_Options.use_tactics ()
                                 in
                              if uu____22801
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____22823  ->
                                     (let uu____22825 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a237  -> ())
                                        uu____22825);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____22868  ->
                                              match uu____22868 with
                                              | (env1,goal,opts) ->
                                                  let uu____22884 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____22884, opts)))))
                              else
                                (let uu____22886 =
                                   let uu____22893 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____22893)  in
                                 [uu____22886])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____22930  ->
                                    match uu____22930 with
                                    | (env1,goal,opts) ->
                                        let uu____22946 = check_trivial goal
                                           in
                                        (match uu____22946 with
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
                                                (let uu____22954 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22955 =
                                                   let uu____22956 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____22957 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____22956 uu____22957
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22954 uu____22955)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____22960 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____22961 =
                                                   let uu____22962 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____22962
                                                    in
                                                 FStar_Errors.diag
                                                   uu____22960 uu____22961)
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
      let uu____22976 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22976 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____22983 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____22983
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____22994 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____22994 with
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
            let uu____23027 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____23027 with
            | FStar_Pervasives_Native.Some uu____23030 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____23050 = acc  in
            match uu____23050 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____23102 = hd1  in
                     (match uu____23102 with
                      | (reason,tm,ctx_u,r) ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____23116 = unresolved ctx_u  in
                             if uu____23116
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___207_23128 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___207_23128.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___207_23128.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___207_23128.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___207_23128.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___207_23128.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___207_23128.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___207_23128.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___207_23128.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___207_23128.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___207_23128.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___207_23128.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___207_23128.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___207_23128.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___207_23128.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___207_23128.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___207_23128.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___207_23128.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___207_23128.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___207_23128.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___207_23128.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___207_23128.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___207_23128.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___207_23128.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___207_23128.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___207_23128.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___207_23128.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___207_23128.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___207_23128.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___207_23128.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___207_23128.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___207_23128.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___207_23128.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___207_23128.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___207_23128.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___207_23128.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___207_23128.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___207_23128.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___207_23128.FStar_TypeChecker_Env.dep_graph)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Normalize.Beta] env1
                                      tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___208_23131 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___208_23131.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___208_23131.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___208_23131.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___208_23131.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___208_23131.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___208_23131.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___208_23131.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___208_23131.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___208_23131.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___208_23131.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___208_23131.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___208_23131.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___208_23131.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___208_23131.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___208_23131.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___208_23131.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___208_23131.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___208_23131.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___208_23131.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___208_23131.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___208_23131.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___208_23131.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___208_23131.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___208_23131.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___208_23131.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___208_23131.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___208_23131.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___208_23131.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___208_23131.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___208_23131.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___208_23131.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___208_23131.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___208_23131.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___208_23131.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___208_23131.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___208_23131.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___208_23131.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.dep_graph =
                                          (uu___208_23131.FStar_TypeChecker_Env.dep_graph)
                                      }
                                    else env1  in
                                  (let uu____23134 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____23134
                                   then
                                     let uu____23135 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____23136 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____23137 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____23138 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____23135 uu____23136 uu____23137
                                       reason uu____23138
                                   else ());
                                  (let g1 =
                                     try
                                       env2.FStar_TypeChecker_Env.check_type_of
                                         must_total env2 tm1
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____23149 =
                                             let uu____23158 =
                                               let uu____23165 =
                                                 let uu____23166 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____23167 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____23168 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____23166 uu____23167
                                                   uu____23168
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____23165, r)
                                                in
                                             [uu____23158]  in
                                           FStar_Errors.add_errors
                                             uu____23149);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___211_23182 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___211_23182.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___211_23182.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___211_23182.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____23185 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____23195  ->
                                               let uu____23196 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____23197 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____23198 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____23196 uu____23197
                                                 reason uu____23198)) env2 g2
                                         true
                                        in
                                     match uu____23185 with
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
          let uu___212_23208 = g  in
          let uu____23209 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___212_23208.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___212_23208.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___212_23208.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____23209
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
        let uu____23259 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____23259 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____23268 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a238  -> ()) uu____23268
      | (reason,e,ctx_u,r)::uu____23273 ->
          let uu____23292 =
            let uu____23297 =
              let uu____23298 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____23299 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____23298 uu____23299 reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____23297)
             in
          FStar_Errors.raise_error uu____23292 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___213_23310 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___213_23310.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___213_23310.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___213_23310.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____23325 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____23325 with
      | FStar_Pervasives_Native.Some uu____23331 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23347 = try_teq false env t1 t2  in
        match uu____23347 with
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
        (let uu____23381 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23381
         then
           let uu____23382 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23383 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____23382
             uu____23383
         else ());
        (let uu____23385 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23385 with
         | (prob,x,wl) ->
             let g =
               let uu____23404 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____23422  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23404  in
             ((let uu____23450 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____23450
               then
                 let uu____23451 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____23452 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____23453 =
                   let uu____23454 = FStar_Util.must g  in
                   guard_to_string env uu____23454  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____23451 uu____23452 uu____23453
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
        let uu____23488 = check_subtyping env t1 t2  in
        match uu____23488 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23507 =
              let uu____23508 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____23508 g  in
            FStar_Pervasives_Native.Some uu____23507
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____23526 = check_subtyping env t1 t2  in
        match uu____23526 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____23545 =
              let uu____23546 =
                let uu____23547 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____23547]  in
              close_guard env uu____23546 g  in
            FStar_Pervasives_Native.Some uu____23545
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____23576 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____23576
         then
           let uu____23577 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____23578 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____23577
             uu____23578
         else ());
        (let uu____23580 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____23580 with
         | (prob,x,wl) ->
             let g =
               let uu____23593 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____23611  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____23593  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____23640 =
                      let uu____23641 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____23641]  in
                    close_guard env uu____23640 g1  in
                  discharge_guard_nosmt env g2))
  